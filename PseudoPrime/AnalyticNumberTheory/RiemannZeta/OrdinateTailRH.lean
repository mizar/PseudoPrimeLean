/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.OrdinateTail
public import Mathlib.NumberTheory.LSeries.RiemannZeta
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCountTailError
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCountErrorNumerics
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCountBudgetRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.CoarseZeroCountNumerics

/-! # Explicit ordinate tail under RH -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Under RH, the inverse-square ordinate tail at `a ≥ 1000` is bounded by
an explicit main term and a logarithmic inverse-square correction. The proof
applies the zero-count budget to the Abel tail estimate. -/
theorem ordinateTail_explicit_of_RH (hRH : RiemannHypothesis) {a : ℝ} (ha : 1000 ≤ a) :
    ordinateTail a ≤
      (1 / Real.pi) * (Real.log a - Real.log (2 * Real.pi) + 1) / a +
        (4 * Real.log a + 1) / a ^ 2 := by
  have hpi : 0 < 2 * Real.pi := mul_pos (by norm_num only) Real.pi_pos
  have hc : Real.log (2 * Real.pi) ≤ Real.log a := by
    apply Real.log_le_log hpi
    linarith only [Real.pi_lt_four, ha]
  have hk : 0 ≤ (1 / Real.pi : ℝ) := div_nonneg (by norm_num only) Real.pi_pos.le
  apply
    ordinateTail_of_log_error hRH (k := 1 / Real.pi) (c := Real.log (2 * Real.pi)) (d := 7 / 4)
      (by linarith only [ha]) hk hc
  intro t ht
  change a ≤ t at ht
  have hbase : 2 * Real.pi * Real.exp 1 ≤ t := by
    have hp :=
      mul_le_mul Real.pi_lt_four.le Real.exp_one_lt_three.le (Real.exp_pos 1).le
        (by norm_num only : (0 : ℝ) ≤ 4)
    nlinarith only [hp, ha, ht]
  have hb := zero_count_budget_of_RH hRH hbase
  have hc := good_count_budget_le_log hbase
  have hid :
    (3 / 4 : ℝ) * Real.log t + 16 / 5 + 2 / (5 * t) =
      2 * ((3 / 8 : ℝ) * Real.log t + 8 / 5 + 1 / (5 * t)) := by
    ring
  rw [hid] at hb
  linarith only [hb, hc]

/-- Under RH, the inverse-square ordinate tail at `a ≥ 1000` is at most
`log a / (πa)`. The explicit RH tail estimate and a numerical absorption
bound give the form used by the normalized Chebyshev estimate. -/
theorem ordinateTail_coarse_of_RH (hRH : RiemannHypothesis) {a : ℝ} (ha : 1000 ≤ a) :
    ordinateTail a ≤ Real.log a / (Real.pi * a) := by
  apply zero_tail_of_preliminary ha
  have h := ordinateTail_explicit_of_RH hRH ha
  have ha0 : 0 < a := by linarith only [ha]
  have hp : (2 * Real.pi : ℝ) ≠ 0 := ne_of_gt (mul_pos (by norm_num only) Real.pi_pos)
  rw [Real.log_div ha0.ne' hp]
  convert h using 1
  ring

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
