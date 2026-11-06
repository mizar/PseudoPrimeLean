/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.FourNinthsCriterion
public import PseudoPrime.PrimeTestBounds.MillerRabin.LeastPrime4136
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! Comparator solution: reproduce the challenge statements and use the library proof. -/

@[expose] public section

namespace ComparatorChallenges

noncomputable def dirichletTrivialZeros {q : ℕ} (χ : DirichletCharacter ℂ q) : Set ℤ := by
  classical
    exact
    if q = 1 then {z | ∃ n : ℕ, z = -2 * ((n : ℤ) + 1)}
    else if χ.Odd then {z | ∃ n : ℕ, z = -2 * (n : ℤ) - 1} else {z | ∃ n : ℕ, z = -2 * (n : ℤ)}

def DirichletRiemannHypothesis {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : Prop :=
  ∀ s : ℂ,
    χ.LFunction s = 0 → s ∉ (Int.cast : ℤ → ℂ) '' dirichletTrivialZeros χ → s.re = (1 : ℝ) / 2

def GeneralizedRiemannHypothesis : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → DirichletRiemannHypothesis χ

def PrimeMillerRabinCriterion : Prop :=
  GeneralizedRiemannHypothesis →
    ∀ n s d : ℕ,
      1 < n →
        Odd n →
        n - 1 = 2 ^ s * d →
        Odd d →
        ((∀ p : ℕ,
            Nat.Prime p →
              (p : ℝ) ≤ 2 * (Real.logb 9 n) ^ 2 →
              ((p : ZMod n) ^ d = 1 ∨ ∃ j : ℕ, j < s ∧ (p : ZMod n) ^ (2 ^ j * d) = -1)) ↔
          Nat.Prime n)

/-- The base-nine cutoff lies below the four-ninths cutoff. A lower bound on
`log 9` gives the coefficient comparison used for prime acceptance. -/
private theorem log_nine_cutoff_le (x : ℝ) :
    2 * (Real.logb 9 x) ^ 2 ≤ (4 / 9 : ℝ) * (Real.log x) ^ 2 := by
  have hlog : Real.log (9 : ℝ) = 2 * Real.log 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num only, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
  have hlow : (219 / 100 : ℝ) < Real.log 9 := by linarith only [hlog, Real.log_three_gt_d9]
  have hsquare : (2 : ℝ) ≤ (4 / 9 : ℝ) * (Real.log 9) ^ 2 := by
    nlinarith only [hlow, sq_nonneg (Real.log 9 - 219 / 100)]
  change 2 * (Real.log x / Real.log 9) ^ 2 ≤ _
  rw [div_pow, ← mul_div_assoc]
  apply (div_le_iff₀ (sq_pos_of_pos (lt_trans (by norm_num only) hlow))).2
  have hmul := mul_nonneg (sub_nonneg.mpr hsquare) (sq_nonneg (Real.log x))
  nlinarith only [hmul]

/-- Under GRH, the prime-base strong test up to the base-nine cutoff characterizes
odd primes greater than one. A rejecting-prime bound handles composites and the
four-ninths acceptance theorem handles primes. -/
theorem prime_millerRabin_log_nine_criterion (hGRH : GeneralizedRiemannHypothesis) {n : ℕ}
    (hn : 1 < n) (ho : Odd n) :
    let (s, d) := Nat.maxPowDvdDiv 2 (n - 1)
    (∀ p : ℕ,
        Nat.Prime p →
          (p : ℝ) ≤ 2 * (Real.logb 9 n) ^ 2 →
          ((p : ZMod n) ^ d = 1 ∨ ∃ j : ℕ, j < s ∧ (p : ZMod n) ^ (2 ^ j * d) = -1)) ↔
      Nat.Prime n := by
  constructor
  · intro hpass
    by_contra hc
    obtain ⟨p, hp, hb, hf⟩ :=
      PseudoPrime.PrimeTestBounds.MillerRabin.exists_prime_reject_le_log9_sq hn ho hc hGRH
    exact hf (hpass p hp hb)
  · intro hp p hprime hb
    exact
      PseudoPrime.PrimeTestBounds.MillerRabin.prime_passes_four_ninths ho hp hprime
        (hb.trans (log_nine_cutoff_le n))

end ComparatorChallenges
