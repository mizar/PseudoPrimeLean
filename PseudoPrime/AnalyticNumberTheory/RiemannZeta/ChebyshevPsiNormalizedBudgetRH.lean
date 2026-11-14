/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.LSeries.RiemannZeta
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiBudgetNormalize
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiBudgetRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.OrdinateTailBudgetRH

/-! # Normalized Chebyshev estimate with the sharp RH zero budget -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Under RH, a positive width `h = x * δ`, cutoff `T ≥ 2 * π * exp 1`, and
`0 ≤ δ ≤ 1/2` give the normalized Chebyshev estimate with the full sharp
zero-count tail. Nonnegativity of the actual ordinate tail justifies applying
the linear power estimates to its certified upper bound. -/
theorem psi_error_normalized_budget_of_RH (hr : RiemannHypothesis) {T x h δ : ℝ}
    (hT : 2 * Real.pi * Real.exp 1 ≤ T) (hx : 0 < x) (hh : 0 < h) (hxh : 1 < x - h) (hd : 0 ≤ δ)
    (hd2 : δ ≤ 1 / 2) (hw : h = x * δ) :
    |Chebyshev.psi x - x| / Real.sqrt x ≤
      h / (2 * Real.sqrt x) + Real.log (2 * Real.pi) / Real.sqrt x +
        (1 + δ / 2) * (Real.log (T / (2 * Real.pi)) ^ 2 / (2 * Real.pi) + 53 / 100) +
        (2 * (1 + δ) / δ) *
          ((Real.log (T / (2 * Real.pi)) + 1) / (Real.pi * T) +
            ((3 / 2 : ℝ) * Real.log T + 271 / 40) / T ^ 2 +
            2 / (3 * T ^ 3)) +
        1 / (h * Real.sqrt x) := by
  have hC0 : 0 ≤ ordinateTail T := by
    rw [ordinateTail_eq]
    exact tsum_nonneg (fun ρ ↦ (ordinateTailWeight_bound hr T ρ).1)
  have hC := hC0.trans (ordinateTail_budget_of_RH hr hT)
  have hA : 0 ≤ Real.log (T / (2 * Real.pi)) ^ 2 / (2 * Real.pi) + 53 / 100 := by
    have h :=
      div_nonneg (sq_nonneg (Real.log (T / (2 * Real.pi))))
        (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2) Real.pi_pos.le)
    linarith only [h]
  exact
    psi_error_budget_normalize hx hw
      (psi_error_budget_scaled hx hh hd hd2 hw hC hA (psi_error_budget_of_RH hr hT hh hxh))

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
