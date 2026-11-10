/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSmoothUpper

/-! # Certified upper smoothed Mangoldt value at 1000 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

-- Exact rational arithmetic verifies the independent finite upper sum.
/-- The rational upper contributions give the stated smoothed sum bound. -/
theorem quarter_smooth_rational_upper :
    (∑ n ∈ refinedEulerPrefixSet, quarterSmoothUpper n (refinedEulerData n)) <
      (986363 / 1000 : ℚ) := by
  decide +kernel

-- Elaborating the 193-element support exceeds the default recursion depth.
set_option maxRecDepth 2000 in
/-- The smoothed Mangoldt sum at 1000 is less than `986363/1000`. Existing
prime-power support and row checks transfer the finite rational certificate. -/
theorem quarter_smooth_1000_upper :
    AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum 1000 < (986363 / 1000 : ℝ) := by
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
    (∑ n ∈ refinedEulerPrefixSet, AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm 1000 n) ≤
      ((∑ n ∈ refinedEulerPrefixSet, quarterSmoothUpper n (refinedEulerData n) : ℚ) : ℝ) := by
    rw [Rat.cast_sum]
    exact Finset.sum_le_sum (fun n hn ↦ quarter_smooth_row_upper (refined_euler_prefix_check n hn))
  have hr := (Rat.cast_lt (K := ℝ)).mpr quarter_smooth_rational_upper
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hr
  rw [he]
  exact hu.trans_lt hr

end PseudoPrime.PrimeTestBounds.MillerRabin
