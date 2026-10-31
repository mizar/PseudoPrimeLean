/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaNearSquareNonOneBounds
public import PseudoPrime.LLS.PaperStatements.GammaNearSquareNonOneBounds
public import PseudoPrime.LLS.GammaQuadraticUniformBounds

/-! # Signed local absorption for negative witnesses from logarithmic scale 1000 -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- At q ≥ 20000 under GRH, L ≥ 1000 and log q ≤ L+7/5, retain the
actual primitive conductor in the upper bound M log(conductor)+22 at x=(2/5)L².
The existing thirty-two-term certificate, pole cost two and left cost 7/100
prove the constant. Retaining the conductor permits local quotient absorption. -/
theorem gamma_primitiveCharacter_sum_re_le_nearSquare_conductor {q : ℕ} [NeZero q] (hq : 20000 ≤ q)
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {L : ℝ} (hL : 1000 ≤ L)
    (hlogq : Real.log q ≤ L + 7 / 5) :
    let x := (2 / 5 : ℝ) * L ^ 2;
    (∑' k : ℕ, gammaMellinKernel.summand χ.primitiveCharacter x k).re ≤
      (11783423 / 25000000 : ℝ) * Real.log χ.conductor + 22 := by
  let x := (2 / 5 : ℝ) * L ^ 2
  have hx : 2 ≤ x := by
    dsimp only [x]
    nlinarith only [hL, sq_nonneg (L - 1000)]
  have he := nearSquare_gamma_error_budgets hL
  have hpole := (nearSquare_gamma_dyadic_pole_budgets hL hlogq).2
  have hu :=
    gamma_primitiveCharacter_sum_re_le_conductor_free_prefix hq χ hne hGRH hx 32
      Analysis.gammaResolvent_thirtyTwo_error_lt
  linarith only [hu, he.1, hpole]

end PseudoPrime.LLS.PaperStatements
