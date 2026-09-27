/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.NumberTheory.Factorization.PollardRho.Basic

/-!
# Pollard rho orbit specifications

This file gives the mathematical orbit underlying the executable Floyd search and relates one
Floyd round to consecutive orbit indices.
-/

namespace PseudoPrime.NumberTheory.Factorization.PollardRho

/-- The `k`th value of the polynomial orbit starting at `seed`. -/
def orbit (n c : ℕ) (seed : ZMod n) : ℕ → ZMod n
  | 0 => seed
  | k + 1 => step n c (orbit n c seed k)

/-- Advancing the orbit by a sum is the same as applying the second number of steps afterward. -/
theorem orbit_add (n c : ℕ) (seed : ZMod n) (a b : ℕ) :
    orbit n c seed (a + b) = orbit n c (orbit n c seed a) b := by
  induction b with
  | zero => rfl
  | succ b ih => rw [Nat.add_succ, orbit, orbit, ih]

/-- The fast Floyd pointer after `k` rounds is the orbit value at index `2*k`. -/
theorem floyd_fast_state (n c : ℕ) (seed : ZMod n) (k : ℕ) :
    orbit n c seed (2 * k) = orbit n c seed (k + k) := by
  congr 1
  exact two_mul k

/-- A single search round computes the gcd associated with the next two Floyd orbit indices. -/
def orbitGcd (n c : ℕ) (seed : ZMod n) (k : ℕ) : ℕ :=
  Nat.gcd (orbit n c seed k - orbit n c seed (2 * k)).val n

/-- A specification version of the Floyd search whose state is named by its orbit offset. -/
def orbitSearch (n c : ℕ) (seed : ZMod n) : ℕ → ℕ → Option ℕ
  | 0, _ => none
  | fuel + 1, offset =>
    let d := orbitGcd n c seed (offset + 1)
    if d = 1 then orbitSearch n c seed fuel (offset + 1)
    else if 1 < d ∧ d < n then some d
    else none

/-- The first round from a seed compares orbit indices one and two. -/
theorem orbitGcd_one (n c : ℕ) (seed : ZMod n) :
    orbitGcd n c seed 1 = Nat.gcd
      (step n c seed - step n c (step n c seed)).val n := by
  rfl

/-- The first recursive state reached after a gcd of one advances the slow pointer by one and the
fast pointer by two orbit steps. -/
theorem floyd_state_succ (n c : ℕ) (seed : ZMod n) (k : ℕ) :
    orbit n c seed (k + 1) = step n c (orbit n c seed k) ∧
    orbit n c seed (2 * (k + 1)) =
      step n c (step n c (orbit n c seed (2 * k))) := by
  constructor
  · rfl
  · have hidx : 2 * (k + 1) = 2 * k + 2 :=
      (Nat.mul_add 2 k 1).trans (congrArg (fun t => 2 * k + t) (Nat.mul_one 2))
    rw [hidx, orbit_add]
    rfl

/-- The executable Floyd transition is the transition between consecutive orbit indices. -/
theorem search_orbit_step (n c fuel : ℕ) (seed : ZMod n) (k : ℕ) :
    search n c (fuel + 1) (orbit n c seed k) (orbit n c seed (2 * k)) =
      (if orbitGcd n c seed (k + 1) = 1 then
        search n c fuel (orbit n c seed (k + 1)) (orbit n c seed (2 * (k + 1)))
      else if 1 < orbitGcd n c seed (k + 1) ∧ orbitGcd n c seed (k + 1) < n then
        some (orbitGcd n c seed (k + 1))
      else none) := by
  obtain ⟨hs, hf⟩ := floyd_state_succ n c seed k
  simp only [search, orbitGcd, hs, hf]

/-- The executable Floyd search agrees with the orbit-indexed specification. -/
theorem search_eq_orbitSearch (n c fuel : ℕ) (seed : ZMod n) (offset : ℕ) :
    search n c fuel (orbit n c seed offset) (orbit n c seed (2 * offset)) =
      orbitSearch n c seed fuel offset := by
  induction fuel generalizing offset with
  | zero => simp only [search, orbitSearch]
  | succ fuel ih =>
    rw [search_orbit_step]
    simp only [orbitSearch]
    split_ifs with hOne hProper
    · exact ih (offset + 1)
    · rfl
    · rfl

/-- If every earlier comparison has gcd one and the requested comparison has a proper gcd, the
orbit-indexed search returns that gcd, provided it has enough rounds. -/
theorem orbitSearch_firstProper (n c : ℕ) (seed : ZMod n) (offset fuel target : ℕ)
    (htarget : 0 < target) (hfuel : target ≤ fuel)
    (hprior : ∀ i, 1 ≤ i → i < target → orbitGcd n c seed (offset + i) = 1)
    (hproper : 1 < orbitGcd n c seed (offset + target) ∧
      orbitGcd n c seed (offset + target) < n) :
    orbitSearch n c seed fuel offset = some (orbitGcd n c seed (offset + target)) := by
  induction target generalizing fuel offset with
  | zero => exact False.elim (Nat.lt_irrefl 0 htarget)
  | succ target ih =>
    cases target with
    | zero =>
      cases fuel with
      | zero => exact False.elim (Nat.not_le_of_gt htarget hfuel)
      | succ fuel =>
        have hdne : orbitGcd n c seed (offset + 1) ≠ 1 := Nat.ne_of_gt hproper.1
        simp only [orbitSearch, hdne, hproper.1, hproper.2, ite_false, and_self, ite_true]
    | succ target =>
      have hfirst : orbitGcd n c seed (offset + 1) = 1 := by
        exact hprior 1 (Nat.le_refl 1) (Nat.succ_lt_succ (Nat.zero_lt_succ target))
      cases fuel with
      | zero => exact False.elim (Nat.not_le_of_gt
          (Nat.zero_lt_succ (target + 1)) hfuel)
      | succ fuel =>
        simp only [orbitSearch, hfirst, ite_true]
        have hprior' : ∀ i, 1 ≤ i → i < target + 1 →
            orbitGcd n c seed (offset + 1 + i) = 1 := by
          intro i hi1 hitarget
          have hi := hprior (i + 1)
            (Nat.le_trans hi1 (Nat.le_add_right i 1)) (Nat.add_lt_add_right hitarget 1)
          have hidx : offset + 1 + i = offset + (i + 1) := by
            calc
              offset + 1 + i = offset + (1 + i) := Nat.add_assoc _ _ _
              _ = offset + (i + 1) := congrArg (fun x => offset + x) (Nat.add_comm 1 i)
          rw [hidx]
          exact hi
        have hshift : offset + 1 + (target + 1) = offset + (target + 1 + 1) := by
          calc
            offset + 1 + (target + 1) = offset + (1 + (target + 1)) := Nat.add_assoc _ _ _
            _ = offset + (target + 1 + 1) :=
              congrArg (fun x => offset + x) (Nat.add_comm 1 (target + 1))
        have hproper' : 1 < orbitGcd n c seed (offset + 1 + (target + 1)) ∧
            orbitGcd n c seed (offset + 1 + (target + 1)) < n := by
          rw [hshift]
          exact hproper
        rw [← hshift]
        exact ih (offset + 1) fuel (Nat.zero_lt_succ target)
          (Nat.succ_le_succ_iff.mp hfuel) hprior' hproper'

/-- On an odd input greater than two, the bounded public search returns the first proper gcd
specified by the polynomial orbit, provided all preceding orbit comparisons have gcd one. -/
theorem findFactor_of_firstProper {n : ℕ} {params : Params} {fuel target : ℕ}
    (hn : 2 < n) (hodd : n % 2 ≠ 0) (htarget : 0 < target) (hfuel : target ≤ fuel)
    (hprior : ∀ i, 1 ≤ i → i < target →
      orbitGcd n params.c (params.seed : ZMod n) i = 1)
    (hproper : 1 < orbitGcd n params.c (params.seed : ZMod n) target ∧
      orbitGcd n params.c (params.seed : ZMod n) target < n) :
    findFactor n params fuel =
      some (orbitGcd n params.c (params.seed : ZMod n) target) := by
  have hfuelNe : fuel ≠ 0 := ne_of_gt (lt_of_lt_of_le htarget hfuel)
  have hnlarge : ¬n ≤ 2 := Nat.not_le_of_gt hn
  have hsearchspec : search n params.c fuel (params.seed : ZMod n) (params.seed : ZMod n) =
      orbitSearch n params.c (params.seed : ZMod n) fuel 0 := by
    simpa only [orbit, Nat.mul_zero] using
      search_eq_orbitSearch n params.c fuel (params.seed : ZMod n) 0
  have hsearch : search n params.c fuel (params.seed : ZMod n) (params.seed : ZMod n) =
      some (orbitGcd n params.c (params.seed : ZMod n) target) := by
    rw [hsearchspec]
    simpa only [Nat.zero_add] using
      orbitSearch_firstProper n params.c (params.seed : ZMod n) 0 fuel target
        htarget hfuel (by simpa only [Nat.zero_add] using hprior)
        (by simpa only [Nat.zero_add] using hproper)
  have heven : ¬ n % 2 = 0 := fun he => hodd he
  simpa only [findFactor, ite_eq_right hfuelNe, ite_eq_right hnlarge,
    ite_eq_right heven] using hsearch

/-- Fuel monotonicity for the public single-attempt function. -/
theorem findFactor_mono_fuel {n : ℕ} {params : Params} {fuel extra factor : ℕ}
    (h : findFactor n params fuel = some factor) :
    findFactor n params (fuel + extra) = some factor := by
  by_cases hf : fuel = 0
  · simp only [findFactor, hf, ite_true] at h
    cases h
  · by_cases hn : n ≤ 2
    · simp only [findFactor, hf, hn, ite_false, ite_true] at h
      cases h
    · by_cases he : n % 2 = 0
      · have htotal : fuel + extra ≠ 0 := by
          intro hzero
          have hpair := Nat.add_eq_zero_iff.mp hzero
          exact hf hpair.1
        have hsmall : factor = 2 := by
          have h' : some 2 = some factor := by
            simpa only [findFactor, ite_eq_right hf, ite_eq_right hn,
              ite_eq_left he] using h
          exact Option.some.inj h'.symm
        subst factor
        simp only [findFactor, ite_eq_right htotal, ite_eq_right hn, ite_eq_left he]
      · have hsearch := search_mono_fuel (n := n) (c := params.c) (fuel := fuel)
          (extra := extra) (x := (params.seed : ZMod n)) (y := (params.seed : ZMod n))
          (by
            have hEq : findFactor n params fuel =
                search n params.c fuel (params.seed : ZMod n) (params.seed : ZMod n) := by
              simp only [findFactor, ite_eq_right hf, ite_eq_right hn, ite_eq_right he]
            rw [hEq] at h
            exact h)
        have htotal : fuel + extra ≠ 0 := by
          intro hzero
          have hpair := Nat.add_eq_zero_iff.mp hzero
          exact hf hpair.1
        simpa only [findFactor, ite_eq_right htotal, ite_eq_right hn,
          ite_eq_right he] using hsearch

end PseudoPrime.NumberTheory.Factorization.PollardRho
