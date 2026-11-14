/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCountIntegratedTailRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroReciprocalFrom40
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroReciprocal40Numerics
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCountBudgetRH
import PseudoPrime.Analysis.LogLinearIntegral
import PseudoPrime.Analysis.LogBudgetIntegral
import PseudoPrime.Analysis.LogTaylorBounds

/-! # Integrated reciprocal-zero estimates without low-zero tables -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Under RH, the centered reciprocal sum retains the height-40 entrance bound and
subtracts the entire pointwise error budget. This prepares the height-100
integrated anchor without a low-zero table. -/
theorem zeroReciprocal_centered_le (hRH : RiemannHypothesis) {T : ℝ} (hT : 40 ≤ T) :
    zeroReciprocalSum T - zeroCountError T / T ≤
      (Real.log T - Real.log (2 * Real.pi)) ^ 2 / (2 * Real.pi) + 2 / 5 -
          ((3 / 4 : ℝ) * Real.log T + 16 / 5 + (2 / 5 : ℝ) / T) / T -
          (3 / 4 : ℝ) / T +
        (2 / 5 : ℝ) / (2 * T ^ 2) := by
  have hbase : 2 * Real.pi * Real.exp 1 ≤ (40 : ℝ) := by
    have hp :=
      mul_le_mul Real.pi_lt_four.le Real.exp_one_lt_three.le (Real.exp_pos 1).le
        (by norm_num only : (0 : ℝ) ≤ 4)
    nlinarith only [hp]
  have hM :
    ContinuousOn (fun t : ℝ ↦ (1 / Real.pi) * t * (Real.log t - Real.log (2 * Real.pi) - 1) + 7 / 4)
      (Set.Icc 40 T) := by
    intro t ht
    have ht0 : t ≠ 0 := by linarith only [ht.1]
    exact
      (((continuousAt_const.mul continuousAt_id).mul
              (((Real.continuousAt_log ht0).sub continuousAt_const).sub continuousAt_const)).add
          continuousAt_const).continuousWithinAt
  have hE :
    ContinuousOn (fun t : ℝ ↦ (3 / 4 : ℝ) * Real.log t + 16 / 5 + (2 / 5 : ℝ) / t)
      (Set.Icc 40 T) := by
    intro t ht
    have ht0 : t ≠ 0 := by linarith only [ht.1]
    exact
      (((continuousAt_const.mul (Real.continuousAt_log ht0)).add continuousAt_const).add
          (continuousAt_const.div continuousAt_id ht0)).continuousWithinAt
  have hQ :
    ∀ t ∈ Set.Icc (40 : ℝ) T,
      |zeroCount t - ((1 / Real.pi) * t * (Real.log t - Real.log (2 * Real.pi) - 1) + 7 / 4)| ≤
        (3 / 4 : ℝ) * Real.log t + 16 / 5 + (2 / 5 : ℝ) / t := by
    intro t ht
    have h := zero_count_budget_of_RH hRH (hbase.trans ht.1)
    convert h using 1
    ring
  have h := reciprocal_sum_retain_count hRH hT hM hE hQ
  have hm :=
    Analysis.log_linear_div_sq_boundary (a := 40) (b := T) (k := 1 / Real.pi) (c :=
      Real.log (2 * Real.pi)) (d := 7 / 4) (by norm_num only) hT
  have he :=
    Analysis.log_budget_div_sq_boundary (a := 40) (b := T) (α := 3 / 4) (β := 16 / 5) (γ := 2 / 5)
      (by norm_num only) hT
  have hk := reciprocal_40_entrance_le
  simp only [zeroCountError, div_eq_mul_inv, mul_inv_rev] at h hm he hk ⊢
  nlinarith only [h, hm, he, hk]

/-- Rational logarithm and π bounds certify the height-100 numerical
comparison needed for the target reciprocal-zero constant. -/
theorem reciprocal_anchor100_numeric :
    (11846 / 10000 : ℝ) - 58 / 100 +
            ((1 / Real.pi) * 100 * (Real.log 100 - Real.log (2 * Real.pi) - 1) + 7 / 4) / 100 -
          (Real.log 100 - Real.log (2 * Real.pi)) ^ 2 / (2 * Real.pi) +
        (16 + (7 / 5 : ℝ) * Real.log 100 + 9 / 10) / 100 ^ 2 ≤
      -(317 / 10000 : ℝ) := by
  have hL :=
    Analysis.rationalLogIntervalCheck_sound
      (show Analysis.rationalLogIntervalCheck 100 6 64 (460517 / 100000) (460518 / 100000) = true
        from by decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hL
  have hc :=
    Analysis.rationalLogIntervalCheck_sound
      (show
        Analysis.rationalLogIntervalCheck (62832 / 10000) 2 64 (18377 / 10000) (18379 / 10000) =
          true
        from by decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hc
  have hcu : Real.log (2 * Real.pi) ≤ (18379 / 10000 : ℝ) := by
    have hp : (2 * Real.pi : ℝ) ≤ 62832 / 10000 := by linarith only [Real.pi_lt_d4]
    have hl := Real.log_le_log (mul_pos (by norm_num only) Real.pi_pos) hp
    linarith only [hl, hc.2]
  have hu : (276727 / 100000 : ℝ) ≤ Real.log 100 - Real.log (2 * Real.pi) := by
    linarith only [hL.1, hcu]
  have hf :
    Real.log 100 - Real.log (2 * Real.pi) - 1 - (Real.log 100 - Real.log (2 * Real.pi)) ^ 2 / 2 ≤
      (276727 / 100000 : ℝ) - 1 - (276727 / 100000 : ℝ) ^ 2 / 2 := by
    have hs := sq_nonneg (Real.log 100 - Real.log (2 * Real.pi) - 276727 / 100000)
    nlinarith only [hu, hs]
  have hp0 : 0 ≤ 1 / Real.pi := one_div_nonneg.mpr Real.pi_pos.le
  have hp : (10000 / 31416 : ℝ) ≤ 1 / Real.pi := by
    apply (le_div_iff₀ Real.pi_pos).2
    nlinarith only [Real.pi_lt_d4]
  have hmul := mul_le_mul_of_nonneg_left hf hp0
  have hneg : (276727 / 100000 : ℝ) - 1 - (276727 / 100000 : ℝ) ^ 2 / 2 ≤ 0 := by norm_num only
  have hmul2 := mul_le_mul_of_nonpos_right hp hneg
  simp only [div_eq_mul_inv, mul_inv_rev] at hmul hmul2 ⊢
  nlinarith only [hmul, hmul2, hL.2]

/-- Under RH, the exact height-100 zero count and reciprocal-sum bound
imply the target integrated reciprocal-zero constant. The remaining tail is
bounded by the moving integrated count error. -/
theorem zeroReciprocalConstant_le_sharp (hRH : RiemannHypothesis) (hc : zeroCount 100 = 58)
    (hs : zeroReciprocalSum 100 ≤ (11846 / 10000 : ℝ)) :
    zeroReciprocalConstant ≤ -(317 / 10000 : ℝ) := by
  have ha :=
    (abs_le.mp (zeroReciprocalConstant_anchor_error hRH (show (100 : ℝ) ≤ 100 by norm_num only))).2
  simp only [zeroCountError, hc] at ha
  have hn := reciprocal_anchor100_numeric
  linarith only [ha, hs, hn]

/-- Under RH, the integrated anchor at height 100 and the retained
height-40 count budget bound the reciprocal-sum constant by `33 / 100`.
The proof uses rational logarithm bounds and does not enumerate zeros. -/
theorem zeroReciprocalConstant_le_thirty_three (hRH : RiemannHypothesis) :
    zeroReciprocalConstant ≤ (33 / 100 : ℝ) := by
  have ha :=
    (abs_le.mp (zeroReciprocalConstant_anchor_error hRH (show (100 : ℝ) ≤ 100 by norm_num only))).2
  have hb := zeroReciprocal_centered_le hRH (show (40 : ℝ) ≤ 100 by norm_num only)
  have hL :=
    Analysis.rationalLogIntervalCheck_sound
      (show Analysis.rationalLogIntervalCheck 100 6 64 (46051 / 10000) (46053 / 10000) = true from
        by decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hL
  norm_num only at ha hb
  linarith only [ha, hb, hL.1, hL.2]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
