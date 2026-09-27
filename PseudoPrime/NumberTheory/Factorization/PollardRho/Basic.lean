/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.NumberTheory.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic

/-!
# Executable Pollard rho search

This module implements a fuel-bounded Floyd cycle search in `ZMod n`. A successful result is a
proper divisor; failure to find one within the supplied trajectory carries no primality information.
-/

namespace PseudoPrime.NumberTheory.Factorization.PollardRho

/-- The two explicit parameters of one Pollard rho trajectory. -/
structure Params where
  /-- Initial point, reduced modulo the input. -/
  seed : ℕ
  /-- Constant term of the map `x ↦ x² + c`, reduced modulo the input. -/
  c : ℕ
  deriving Repr, DecidableEq

/-- One executable iteration of the polynomial used by Pollard rho. -/
def step (n c : ℕ) (x : ZMod n) : ZMod n := x * x + (c : ZMod n)

/-- Floyd's tortoise and hare search. One fuel unit performs three polynomial steps and one gcd. -/
def search (n c fuel : ℕ) (x y : ZMod n) : Option ℕ :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    let x' := step n c x
    let y' := step n c (step n c y)
    let d := Nat.gcd (x' - y').val n
    if d = 1 then search n c fuel x' y'
    else if 1 < d ∧ d < n then some d
    else none
termination_by fuel

/-- Run one bounded Pollard rho attempt. Fuel zero always returns `none`; inputs at most two
return `none`; even inputs greater than two immediately return the factor two. On odd inputs the
function runs Floyd's search from the supplied seed. `none` means only that this attempt did not
find a proper factor. -/
def findFactor (n : ℕ) (params : Params) (fuel : ℕ) : Option ℕ :=
  if fuel = 0 then none
  else if n ≤ 2 then none
  else if n % 2 = 0 then some 2
  else search n params.c fuel (params.seed : ZMod n) (params.seed : ZMod n)

/-- Any positive-budget attempt on an even input greater than two returns the factor two before
starting the Floyd trajectory. This exposes the deterministic even-input branch to BLS factor
supply and other callers without unfolding the executable search. -/
theorem findFactor_eq_some_two_of_even {n fuel : ℕ} (params : Params)
    (hfuel : 0 < fuel) (hn : 2 < n) (heven : n % 2 = 0) :
    findFactor n params fuel = some 2 := by
  unfold findFactor
  rw [ite_eq_right (Nat.ne_of_gt hfuel), ite_eq_right (Nat.not_le_of_gt hn), ite_eq_left heven]

/-- Parameters and an individual round budget for one deterministic retry. -/
structure Attempt where
  /-- Trajectory parameters for this attempt. -/
  params : Params
  /-- Maximum Floyd rounds in this attempt. -/
  fuel : ℕ
  deriving Repr, DecidableEq

/-- Try a finite, caller-supplied schedule and return the first factor found. -/
def findFactorMany (n : ℕ) : List Attempt → Option ℕ
  | [] => none
  | attempt :: attempts =>
    match findFactor n attempt.params attempt.fuel with
    | some d => some d
    | none => findFactorMany n attempts

/-- Every value returned by the Floyd search is a proper divisor of the modulus. -/
theorem search_sound {n c fuel : ℕ} {x y : ZMod n} {factor : ℕ}
    (h : search n c fuel x y = some factor) : ProperFactor n factor := by
  induction fuel generalizing x y factor with
  | zero =>
    simp only [search] at h
    cases h
  | succ fuel ih =>
    simp only [search] at h
    let x' := step n c x
    let y' := step n c (step n c y)
    let g := Nat.gcd (x' - y').val n
    by_cases hg : g = 1
    · simp only [x', y', g, ite_eq_left hg] at h
      exact ih h
    · by_cases hp : 1 < g ∧ g < n
      · simp only [x', y', g, ite_eq_right hg, ite_eq_left hp] at h
        change some g = some factor at h
        have hgf : g = factor := Option.some.inj h
        subst factor
        exact ⟨hp.1, hp.2, Nat.gcd_dvd_right _ _⟩
      · simp only [x', y', g, ite_eq_right hg, ite_eq_right hp] at h
        cases h

/-- Once a search finds its first factor, additional fuel preserves that result. -/
theorem search_mono_fuel {n c fuel extra : ℕ} {x y : ZMod n} {factor : ℕ}
    (h : search n c fuel x y = some factor) :
    search n c (fuel + extra) x y = some factor := by
  induction fuel generalizing x y factor with
  | zero =>
    simp only [search] at h
    cases h
  | succ fuel ih =>
    have hsum : fuel + 1 + extra = (fuel + extra) + 1 := by
      calc
        fuel + 1 + extra = fuel + (1 + extra) := Nat.add_assoc _ _ _
        _ = fuel + (extra + 1) := congrArg (fuel + ·) (Nat.add_comm 1 extra)
        _ = (fuel + extra) + 1 := (Nat.add_assoc _ _ _).symm
    rw [hsum]
    simp only [search] at h ⊢
    let x' := step n c x
    let y' := step n c (step n c y)
    let g := Nat.gcd (x' - y').val n
    by_cases hg : g = 1
    · simp only [x', y', g, ite_eq_left hg] at h ⊢
      exact ih h
    · by_cases hp : 1 < g ∧ g < n
      · simp only [x', y', g, ite_eq_right hg, ite_eq_left hp] at h ⊢
        exact h
      · simp only [x', y', g, ite_eq_right hg, ite_eq_right hp] at h
        cases h

/-- A successful bounded attempt always returns a proper factor. -/
theorem findFactor_sound {n : ℕ} {params : Params} {fuel factor : ℕ}
    (h : findFactor n params fuel = some factor) : ProperFactor n factor := by
  by_cases hf : fuel = 0
  · simp only [findFactor, hf, ite_true] at h
    cases h
  · by_cases hn : n ≤ 2
    · simp only [findFactor, hf, hn, ite_false, ite_true] at h
      cases h
    · by_cases he : n % 2 = 0
      · simp only [findFactor, hf, hn, he, ↓reduceIte] at h
        have hf2 : factor = 2 := Option.some.inj h.symm
        subst factor
        refine ⟨by decide, ?_, Nat.dvd_of_mod_eq_zero he⟩
        exact Nat.lt_of_not_ge hn
      · exact search_sound (n := n) (c := params.c) (fuel := fuel)
          (x := (params.seed : ZMod n)) (y := (params.seed : ZMod n))
          (by simpa only [findFactor, hf, hn, he, ite_false] using h)

/-- Every factor returned by a finite retry schedule is a proper divisor. -/
theorem findFactorMany_sound {n factor : ℕ} {attempts : List Attempt}
    (h : findFactorMany n attempts = some factor) : ProperFactor n factor := by
  induction attempts with
  | nil =>
    simp only [findFactorMany] at h
    cases h
  | cons attempt attempts ih =>
    simp only [findFactorMany] at h
    cases htry : findFactor n attempt.params attempt.fuel with
    | none => exact ih (by simpa only [htry] using h)
    | some d =>
      have hEq : d = factor := Option.some.inj (by simpa only [htry] using h)
      subst factor
      exact findFactor_sound htry

/-- A prime input never yields a factor, for any parameters or fuel. -/
theorem none_of_prime {n : ℕ} (hn : Nat.Prime n) (params : Params) (fuel : ℕ) :
    findFactor n params fuel = none := by
  cases h : findFactor n params fuel with
  | none => rfl
  | some d =>
    have hd := findFactor_sound h
    change 1 < d ∧ d < n ∧ d ∣ n at hd
    have hd' : d = 1 ∨ d = n := (Nat.dvd_prime hn).mp hd.2.2
    rcases hd' with hd1 | hdn
    · exact False.elim ((Nat.ne_of_gt hd.1) hd1)
    · exact False.elim ((Nat.ne_of_lt hd.2.1) hdn)

end PseudoPrime.NumberTheory.Factorization.PollardRho
