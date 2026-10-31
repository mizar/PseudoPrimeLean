/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.GammaNearSquareNumerics
public import PseudoPrime.LLS.PaperStatements.GammaNearSquareNonOneBounds

/-! # Quadratic non-one witnesses at near-square scale from log 1000 -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Under GRH at even q ≥ 20000, a nonprincipal quadratic character has
an odd prime with value different from one below (99/100)L² whenever
L ≥ 1000 and log q ≤ L+7/5. Combine the certified actual principal/ramp
bounds with the uniform primitive sum and dyadic correction. The strict
gap is proved on the entire half-line and is not an additional assumption. -/
theorem exists_odd_prime_ne_one_of_nearSquare_gamma_endpoint {q : ℕ} [NeZero q] (hq : 20000 ≤ q)
    (χ : DirichletCharacter ℂ q) (hquad : χ.IsQuadratic) (hne : χ ≠ 1) (h2 : 2 ∣ q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {L : ℝ} (hL : 1000 ≤ L)
    (hlogq : Real.log q ≤ L + 7 / 5) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ (99 / 100 : ℝ) * L ^ 2 ∧ χ p ≠ 1 := by
  let x := (2 / 5 : ℝ) * L ^ 2
  have hx : 1 ≤ x := by
    dsimp only [x]
    nlinarith only [hL, sq_nonneg (L - 1000)]
  have hx0 := zero_lt_one.trans_le hx
  have he := PaperStatements.nearSquare_gamma_error_budgets hL
  have htwo := (PaperStatements.nearSquare_gamma_dyadic_pole_budgets hL hlogq).1
  have hu :=
    PaperStatements.gamma_primitiveCharacter_sum_re_le_nearSquare_endpoint hq χ hne hGRH hL hlogq
  have hP := gamma_level_one_sum_upper_variable hGRH.riemann hx
  have hT := gamma_ramp_sum_lower_variable hGRH.riemann hx
  have hgap :
    (∑' k : ℕ, PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x k).re +
        (∑' k : ℕ, PaperStatements.gammaMellinKernel.summand χ.primitiveCharacter x k).re +
        (Real.log ((99 / 40 : ℝ) * x) + Real.log 2) / Real.sqrt x <
      2 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x) := by
    nlinarith only [hu, hP, hT, he.2.1, he.2.2.1, he.2.2.2.2, htwo, hL]
  obtain ⟨p, hp, ho, hb, hv⟩ :=
    exists_odd_prime_ne_one_of_gamma_ramp_gap χ hquad h2 hx0
      (show 1 ≤ (99 / 40 : ℝ) * x by linarith only [hx]) hgap
  refine ⟨p, hp, ho, ?_, hv⟩
  dsimp only [x] at hb
  nlinarith only [hb]

end PseudoPrime.LLS
