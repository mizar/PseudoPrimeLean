/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.Below64MainErrorBounds

/-! # Reciprocal main errors down to cutoff 53/2 -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Input: a real cutoff at least 53/2.
Claim: the reciprocal main error is at most -1/4.
Proof: retain the reciprocal factor and use the existing Euler and logarithm bounds.
Role: extend the reciprocal-only analytic comparison to the smaller cutoff regime. -/
theorem primitiveReciprocalOddMainError_le_fixed_of_ge_twenty_six_half {x : ℝ} (hx : 53 / 2 ≤ x) :
    primitiveReciprocalOddMainError x ≤ -(1 / 4 : ℝ) := by
  have hxp : 0 < x := by linarith only [hx]
  have hi : 1 / x ≤ (2 / 53 : ℝ) := by
    have h :=
      div_le_div_of_nonneg_left (by norm_num only : (0 : ℝ) ≤ 1)
        (by norm_num only : (0 : ℝ) < 53 / 2) hx
    norm_num only [one_div_div] at h
    exact h
  have hc : 0 ≤ 1 - 1 / x := by linarith only [hi]
  have hg := mul_le_mul_of_nonneg_right twentyThree_fortieths_lt_eulerMascheroniConstant.le hc
  have hl := mul_le_mul_of_nonneg_right Real.log_two_lt_d9.le (inv_nonneg.mpr hxp.le)
  unfold primitiveReciprocalOddMainError
  simp only [div_eq_mul_inv] at hi hg ⊢
  nlinarith only [hg, hl, hi]

/-- Input: a real cutoff at least 53/2.
Claim: the reciprocal main error is at most -1/4.
Proof: retain the reciprocal factor and use the existing Euler and logarithm bounds.
Role: extend the reciprocal-only analytic comparison to the smaller cutoff regime. -/
theorem primitiveReciprocalEvenMainError_le_fixed_of_ge_twenty_six_half {x : ℝ} (hx : 53 / 2 ≤ x) :
    primitiveReciprocalEvenMainError x ≤ -(1 / 4 : ℝ) := by
  have hxp : 0 < x := by linarith only [hx]
  have hi : 1 / x ≤ (2 / 53 : ℝ) := by
    have h :=
      div_le_div_of_nonneg_left (by norm_num only : (0 : ℝ) ≤ 1)
        (by norm_num only : (0 : ℝ) < 53 / 2) hx
    norm_num only [one_div_div] at h
    exact h
  have hc : 0 ≤ 1 - 1 / x := by linarith only [hi]
  have hg := mul_le_mul_of_nonneg_right Real.one_half_lt_eulerMascheroniConstant.le hc
  have hlog : 0 ≤ Real.log x := Real.log_nonneg (by linarith only [hx])
  have hr : (Real.log x + 1) / x ≤ logLinearRatio x := by
    unfold logLinearRatio
    exact div_le_div_of_nonneg_right (by linarith only [hlog]) hxp.le
  have hm :=
    strictAntiOn_logLinearRatio.antitoneOn (by norm_num only [Set.mem_Ici])
      (by
        simp only [Set.mem_Ici]; linarith only [hx])
      hx
  have hb : Real.log (53 / 2 : ℝ) ≤ 4 := by
    have ht : rationalLogIntervalCheck (53 / 2) 5 10 3 4 = true := by decide +kernel
    have h := (rationalLogIntervalCheck_sound ht).2
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    exact h
  unfold logLinearRatio at hr hm
  unfold primitiveReciprocalEvenMainError
  simp only [div_eq_mul_inv] at hr hm hg ⊢
  nlinarith only [hr, hm, hb, hg, Real.log_two_gt_d9]

end PseudoPrime.Analysis
