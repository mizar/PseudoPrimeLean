/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroReciprocalIntegratedRH
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.OrdinateTailRetainedRH
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiSign100RH
public import PseudoPrime.Analysis.NumericalLogBounds

/-! # Height-100 boundary terms for the sinc-weighted zero sum -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Under RH and the exact height-100 count, the reciprocal constant minus the actual
height-100 sum is at most −12163/10000. Keeping the sum symbolic in the anchor
gives the boundary term for weighted Abel summation. -/
theorem reciprocal_anchor100_sub_sum (hRH : RiemannHypothesis) :
    zeroReciprocalConstant - zeroReciprocalSum 100 ≤ -(12163 / 10000 : ℝ) := by
  have ha := (abs_le.mp (zeroReciprocalConstant_anchor_error hRH (T := 100) le_rfl)).2
  simp only [zeroCountError, count_100_eq_58_of_RH hRH] at ha
  linarith only [ha, reciprocal_anchor100_numeric]

/-- Under RH the inverse-square ordinate tail above 100 contributes at most 13/1000.
The negative endpoint term retains all 58 zeros through the cutoff. -/
theorem ordinateTail_hundred_le (hRH : RiemannHypothesis) : ordinateTail 100 ≤ (13 / 1000 : ℝ) := by
  have ht := ordinateTail_retain_count hRH (a := 100) (by norm_num only)
  rw [count_100_eq_58_of_RH hRH] at ht
  have hl := Analysis.log_hundred_le_fourHundredSixtyThree_hundredths
  have hd : Real.log 100 - Real.log (2 * Real.pi) ≤ 2793 / 1000 := by
    linarith only [hl, Analysis.log_two_mul_pi_gt]
  have hp : 2 / Real.pi ≤ (20000 / 31415 : ℝ) := by
    apply (div_le_iff₀ Real.pi_pos).2
    linarith only [Real.pi_gt_d4]
  have hm :=
    mul_le_mul_of_nonneg_left hd (div_nonneg (by norm_num only : (0 : ℝ) ≤ 2) Real.pi_pos.le)
  have hn := mul_le_mul_of_nonneg_right hp (by norm_num only : (0 : ℝ) ≤ 2793 / 1000)
  linarith only [ht, hm, hn, hl]

/-- The anchor and the three-halves damping correction give a single RH tail budget. -/
theorem sincTail_anchor_le (hRH : RiemannHypothesis) :
    zeroReciprocalConstant - zeroReciprocalSum 100 + 3 / 2 * ordinateTail 100 ≤
      -(748 / 625 : ℝ) := by
  linarith only [reciprocal_anchor100_sub_sum hRH, ordinateTail_hundred_le hRH]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
