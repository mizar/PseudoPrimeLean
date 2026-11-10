/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleEulerPsi
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.WeightedMangoldt

/-! Certified lower bound for the smoothed Mangoldt sum at 1000. -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

set_option maxRecDepth 1000000 in
-- Kernel reduction checks the finite rational certificate.
/-- Check a rational interval enclosing the logarithm of 1000. -/
theorem refined_log_1000_check :
    Analysis.rationalLogIntervalCheck 1000 (Nat.log2 1000 + 1) 24 (6907755 / 1000000)
        (6907756 / 1000000) =
      true := by
  decide +kernel

/-- A rational lower bound for the logarithm of 1000. -/
theorem refined_log_1000_lower : (6907755 / 1000000 : ℝ) ≤ Real.log 1000 := by
  have h := Analysis.rationalLogIntervalCheck_sound refined_log_1000_check
  norm_num only at h ⊢
  exact h.1

/-- A rational lower contribution to the smoothed Mangoldt sum for a prime-power row. -/
def refinedSmoothLower (n : ℕ) (r : RefinedEulerAtom) : ℚ :=
  if IsPrimePow n then r.lo * (6907755 / 1000000) - r.k * r.hi ^ 2 else 0

/-- A checked row supplies a lower bound for its smoothed Mangoldt term. -/
theorem refined_smooth_row_lower {n : ℕ} {r : RefinedEulerAtom}
    (hc : IsPrimePow n → refinedEulerAtomCheck 24 n r = true) :
    (refinedSmoothLower n r : ℝ) ≤
      AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm 1000 n := by
  by_cases hn : IsPrimePow n
  · have h := hc hn
    simp only [refinedEulerAtomCheck, Bool.and_eq_true, decide_eq_true_eq] at h
    have hl := Analysis.rationalLogIntervalCheck_sound h.2.1
    simp only [Rat.cast_natCast] at hl
    have hp0 : 0 ≤ Real.log r.p := Real.log_natCast_nonneg r.p
    have hsq := pow_le_pow_left₀ hp0 hl.2 2
    have hmul := mul_le_mul hl.1 refined_log_1000_lower (by norm_num only) hp0
    have hk := mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg r.k : (0 : ℝ) ≤ r.k)
    have ht :=
      AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm_prime_pow
        (by norm_num only : (1000 : ℝ) ≠ 0) h.1.1 h.1.2.1
    rw [h.1.2.2.1] at ht
    simp only [refinedSmoothLower, ite_eq_left hn, Rat.cast_sub, Rat.cast_mul, Rat.cast_div,
      Rat.cast_ofNat, Rat.cast_natCast, Rat.cast_pow]
    rw [ht]
    nlinarith only [hmul, hk]
  · have hz :=
      AnalyticNumberTheory.Arithmetic.logMangoldtTerm_eq_zero_of_not_primePow (x := (1000 : ℝ)) hn
    simp only [refinedSmoothLower, ite_eq_right hn, Rat.cast_zero, hz, le_refl]

set_option maxRecDepth 1000000 in
-- Kernel reduction checks the finite rational certificate.
/-- The rational lower row sum is greater than 24659/25. -/
theorem refined_smooth_rational_lower :
    (24659 / 25 : ℚ) < ∑ n ∈ refinedEulerPrefixSet, refinedSmoothLower n (refinedEulerData n) := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The smoothed Mangoldt sum at 1000 exceeds 24659/25. -/
theorem refined_smooth_1000_lower :
    (24659 / 25 : ℝ) < AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum 1000 := by
  have he :
    AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum 1000 =
      ∑ n ∈ refinedEulerPrefixSet,
        AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm 1000 n := by
    simp only [AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum, Nat.floor_ofNat]
    symm
    apply Finset.sum_subset refined_euler_prefix_subset
    intro n hn hn'
    have hnp : ¬IsPrimePow n := fun hp ↦ hn' (refined_euler_prefix_support n hn hp)
    exact AnalyticNumberTheory.Arithmetic.logMangoldtTerm_eq_zero_of_not_primePow hnp
  have hu :
    ((∑ n ∈ refinedEulerPrefixSet, refinedSmoothLower n (refinedEulerData n) : ℚ) : ℝ) ≤
      ∑ n ∈ refinedEulerPrefixSet,
        AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm 1000 n := by
    rw [Rat.cast_sum]
    exact Finset.sum_le_sum (fun n hn ↦ refined_smooth_row_lower (refined_euler_prefix_check n hn))
  have hr :
    (((24659 / 25 : ℚ) : ℝ)) <
      ((∑ n ∈ refinedEulerPrefixSet, refinedSmoothLower n (refinedEulerData n) : ℚ) : ℝ) :=
    Rat.cast_lt.mpr refined_smooth_rational_lower
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hr
  rw [he]
  exact hr.trans_le hu

end PseudoPrime.PrimeTestBounds.MillerRabin
