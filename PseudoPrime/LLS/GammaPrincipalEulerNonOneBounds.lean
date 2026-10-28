/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaConductorFreeNonOneBounds
public import PseudoPrime.LLS.GammaPrincipalEulerCharacterBounds
public import PseudoPrime.LLS.GammaRetainedCommonCostBounds
public import PseudoPrime.Analysis.LLSGammaPrincipalEulerNonOneBounds2

/-! # Non-one witnesses from retained real-axis Euler budgets -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Under GRH, a nonprincipal even quadratic character at even level q ≥ 20000
has an odd-prime non-one witness through (4/5)L² when L ≥ 22221 and log q ≤ L+7/5.
Retain parity through primitivization and use common Euler cost 541/50.
This improves the starting scale for positive-input quadratic characters. -/
theorem exists_odd_prime_ne_one_of_even_gamma_log_22221 {q : ℕ} [NeZero q] (hq : 20000 ≤ q)
    (χ : DirichletCharacter ℂ q) (hquad : χ.IsQuadratic) (hne : χ ≠ 1) (heven : χ.Even) (h2 : 2 ∣ q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {L : ℝ} (hL : 22221 ≤ L)
    (hlogq : Real.log q ≤ L + 7 / 5) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ (4 / 5 : ℝ) * L ^ 2 ∧ χ p ≠ 1 := by
  apply
    exists_odd_prime_ne_one_of_log_ratio_character_budget χ hquad h2 hGRH (by linarith only [hL])
      (Analysis.nonOne_log_ratio_of_ge_22221 hL) hlogq (C := 541 / 50)
  · exact
      (PaperStatements.gamma_primitiveCharacter_sum_re_lt_common_euler_cost hq χ hne hGRH
          (by nlinarith only [hL, sq_nonneg (L - 22221)])
          (gamma_even_common_cost_lt_precise hGRH.riemann
            ((NumberTheory.primitiveCharacter_even_iff χ).mpr heven))).le
  · linarith only [hL]

end PseudoPrime.LLS
