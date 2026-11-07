/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleEulerPrefixUpper

/-! Certified lower bound for Chebyshev psi at 1000. -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The rational lower contribution to Chebyshev psi for a certified prime-power row. -/
def refinedPsiLower (n : ℕ) (r : RefinedEulerAtom) : ℚ :=
  if IsPrimePow n then r.lo else 0

/-- Each checked prime-power row gives a lower bound for its von Mangoldt value. -/
theorem refined_psi_row_lower {n : ℕ} {r : RefinedEulerAtom}
    (hc : IsPrimePow n → refinedEulerAtomCheck 24 n r = true) :
    (refinedPsiLower n r : ℝ) ≤ ArithmeticFunction.vonMangoldt n := by
  by_cases hn : IsPrimePow n
  · have h := hc hn
    simp only [refinedEulerAtomCheck, Bool.and_eq_true, decide_eq_true_eq] at h
    have hl := Analysis.rationalLogIntervalCheck_sound h.2.1
    simp only [Rat.cast_natCast] at hl
    have hΛ : ArithmeticFunction.vonMangoldt n = Real.log r.p := by
      rw [← h.1.2.2.1, ArithmeticFunction.vonMangoldt_apply_pow h.1.2.1,
        ArithmeticFunction.vonMangoldt_apply_prime h.1.1]
    simpa only [refinedPsiLower, ite_eq_left hn, hΛ] using hl.1
  · have hz := ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn
    simp only [refinedPsiLower, ite_eq_right hn, Rat.cast_zero, hz, le_refl]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Kernel reduction checks the finite rational sum.
/-- The rational lower row sum is greater than 24917/25. -/
theorem refined_psi_rational_lower :
    (24917 / 25 : ℚ) < ∑ n ∈ refinedEulerPrefixSet, refinedPsiLower n (refinedEulerData n) := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The Chebyshev psi value at 1000 exceeds 24917/25. -/
theorem refined_psi_1000_lower : (24917 / 25 : ℝ) < Chebyshev.psi 1000 := by
  have he : Chebyshev.psi 1000 = ∑ n ∈ refinedEulerPrefixSet, ArithmeticFunction.vonMangoldt n := by
    simp only [Chebyshev.psi, Nat.floor_ofNat]
    symm
    apply Finset.sum_subset refined_euler_prefix_subset
    intro n hn hn'
    have hnp : ¬IsPrimePow n := fun hp ↦ hn' (refined_euler_prefix_support n hn hp)
    exact ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hnp
  have hu :
    ((∑ n ∈ refinedEulerPrefixSet, refinedPsiLower n (refinedEulerData n) : ℚ) : ℝ) ≤
      ∑ n ∈ refinedEulerPrefixSet, ArithmeticFunction.vonMangoldt n := by
    rw [Rat.cast_sum]
    exact Finset.sum_le_sum (fun n hn ↦ refined_psi_row_lower (refined_euler_prefix_check n hn))
  have hr :
    (((24917 / 25 : ℚ) : ℝ)) <
      ((∑ n ∈ refinedEulerPrefixSet, refinedPsiLower n (refinedEulerData n) : ℚ) : ℝ) :=
    Rat.cast_lt.mpr refined_psi_rational_lower
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hr
  rw [he]
  exact hr.trans_le hu

end PseudoPrime.PrimeTestBounds.MillerRabin
