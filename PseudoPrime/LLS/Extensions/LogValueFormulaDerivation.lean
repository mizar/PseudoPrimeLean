/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Extensions.PaperStatements
public import PseudoPrime.LLS.Extensions.CompletedZeroMass
public import PseudoPrime.LLS.Extensions.LogValueFormula
public import PseudoPrime.LLS.Extensions.ShiftedFormulaIntegration

/-!
# Deriving the generalized logarithmic formula

An exact shifted formula gives the integrated decomposition and its bounded error terms.
-/

@[expose] public section

namespace PseudoPrime.LLS.Extensions

/-- For every admissible function under individual RH, an exact decomposition into the
integrated completed-zero and gamma contributions implies the generalized Lemma 2.5.
Order-at-most-one growth proves mass convergence; the integral estimates supply the two
bounded coefficients. Only the exact analytic decomposition remains as an input. -/
theorem lls_propL1_general_of_integrated_decomposition
    (hformula :
      ∀ f : GeneralLFunction,
        f.IsAdmissible →
          f.RiemannHypothesis →
          ∀ x : ℝ,
            2 ≤ x →
              Real.log ‖f.L 1‖ =
                (f.logValueSum x).re + f.gammaLogDerivativeAtOne / Real.log x -
                    f.zeroMass / (2 * Real.log x) -
                    ((∫ σ : ℝ in Set.Ioi 1, f.shiftedZeroSum x σ) / (Real.log x : ℂ)).re +
                  (f.gammaLogRemainder x).re) :
    lls_propL1_general := by
  intro f hf hRH
  have hm := GeneralLFunction.summable_zeroMassTerm_of_admissible f hf hRH
  refine ⟨hm, ?_⟩
  intro x hx
  exact
    GeneralLFunction.logValueFormula_of_integrated_contributions f hRH hm hf.2.2.2.1
      (lt_of_lt_of_le (by norm_num only : (1 : ℝ) < 2) hx) (hformula f hf hRH x hx)

/-- An exact shifted logarithmic formula for admissible RH functions implies the
generalized Lemma 2.5. The arithmetic integral, origin endpoint, zero-mass convergence
and both error estimates are proved independently; only the shifted formula is assumed. -/
theorem lls_propL1_general_of_shifted_formula
    (hformula :
      ∀ f : GeneralLFunction,
        f.IsAdmissible →
          f.RiemannHypothesis →
          ∀ x : ℝ,
            2 ≤ x →
              ∀ σ : ℝ,
                1 < σ →
                  f.shiftedArithmeticSum x σ =
                    deriv
                          (AnalyticNumberTheory.General.shiftedLogarithmicRegularization f.L x
                            (σ : ℂ))
                          0 +
                        f.shiftedZeroSum x σ -
                      f.shiftedGammaSum x σ) :
    lls_propL1_general := by
  apply lls_propL1_general_of_integrated_decomposition
  intro f hf hRH x hx
  exact
    GeneralLFunction.integrated_decomposition_of_shifted_formula f hf hRH
      (lt_of_lt_of_le (show (1 : ℝ) < 2 by norm_num only) hx) (hformula f hf hRH x hx)

end PseudoPrime.LLS.Extensions
