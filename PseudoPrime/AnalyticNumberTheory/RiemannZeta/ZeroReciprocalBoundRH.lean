/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeightCounting
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroReciprocalCountRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCountBudgetRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.CoarseZeroCountNumerics

/-! # Refined reciprocal zero-sum bound under RH -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Under RH, the reciprocal-height zero sum through `b ≥ 2πe` obeys the
explicit logarithmic bound with the entrance constant and negative correction.
The RH zero-count budget supplies the finite-range hypothesis. -/
theorem zeroReciprocal_bound_of_RH (hRH : RiemannHypothesis) {b : ℝ}
    (hb : 2 * Real.pi * Real.exp 1 ≤ b) :
    zeroReciprocalSum b ≤
      (Real.log (b / (2 * Real.pi))) ^ 2 / (2 * Real.pi) + 4 / 5 - 1 / (2 * Real.pi) := by
  apply zeroReciprocal_bound_of_count hRH hb
  intro t ht
  have hb := zero_count_budget_of_RH hRH ht.1
  have hc := good_count_budget_le_log ht.1
  have hid :
    (3 / 4 : ℝ) * Real.log t + 16 / 5 + 2 / (5 * t) =
      2 * ((3 / 8 : ℝ) * Real.log t + 8 / 5 + 1 / (5 * t)) := by
    ring
  rw [hid] at hb
  linarith only [hb, hc]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
