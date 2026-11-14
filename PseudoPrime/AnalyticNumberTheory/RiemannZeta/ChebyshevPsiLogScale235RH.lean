/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.LSeries.RiemannZeta
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiBudgetRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLogScaleConditions235

/-! # RH Chebyshev error at the 23.5 logarithmic scale -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Under RH at logarithmic height `L ≥ 47/2`, substitute the width
`5L exp(L/2)/(6π)` and its matching cutoff into the explicit zero-budget
estimate. This is the unnormalized input for the Lee–Nosal envelope. -/
theorem psi_error_scale235_of_RH (hRH : RiemannHypothesis) {L : ℝ} (hL : (47 / 2 : ℝ) ≤ L) :
    let x := Real.exp L
    let h := (5 * L / (6 * Real.pi)) * Real.exp (L / 2)
    let T := 12 * Real.pi * Real.exp (L / 2) / (5 * L)
    |Chebyshev.psi x - x| ≤
      h / 2 + Real.log (2 * Real.pi) +
        Real.sqrt (x + h) * (Real.log (T / (2 * Real.pi)) ^ 2 / (2 * Real.pi) + 53 / 100) +
        ((x + h) ^ (3 / 2 : ℝ) + x ^ (3 / 2 : ℝ)) / h *
          ((Real.log (T / (2 * Real.pi)) + 1) / (Real.pi * T) +
            ((3 / 2 : ℝ) * Real.log T + 271 / 40) / T ^ 2 +
            2 / (3 * T ^ 3)) +
        1 / h := by
  dsimp only
  have hc := scale235_conditions hL
  have hbase : 2 * Real.pi * Real.exp 1 ≤ (2000 : ℝ) := by
    have hp :=
      mul_le_mul Real.pi_lt_four.le Real.exp_one_lt_three.le (Real.exp_pos 1).le
        (by norm_num only : (0 : ℝ) ≤ 4)
    nlinarith only [hp]
  exact psi_error_budget_of_RH hRH (hbase.trans hc.2.2.2.2) hc.2.2.1 hc.2.2.2.1

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
