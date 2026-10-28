/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaConductorFreeNonOneBounds
public import PseudoPrime.LLS.GammaPrincipalEulerCharacterBounds
public import PseudoPrime.LLS.GammaRetainedCommonCostBounds
public import PseudoPrime.Analysis.LLSGammaPrincipalEulerNonOneBounds

/-! # Non-one witnesses from retained real-axis Euler budgets -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Under GRH, a nonprincipal quadratic character of even level q ≥ 20000 has
an odd-prime non-one witness at most (4/5)L² if L ≥ 22920 and log q ≤ L+7/5.
Use the signed real-axis Euler bound with cost 117/10 in the generic comparison.
This lowers the starting point without adding a numerical prefix certificate. -/
theorem exists_odd_prime_ne_one_of_gamma_log_22920 {q : ℕ} [NeZero q] (hq : 20000 ≤ q)
    (χ : DirichletCharacter ℂ q) (hquad : χ.IsQuadratic) (hne : χ ≠ 1) (h2 : 2 ∣ q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {L : ℝ} (hL : 22920 ≤ L)
    (hlogq : Real.log q ≤ L + 7 / 5) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ (4 / 5 : ℝ) * L ^ 2 ∧ χ p ≠ 1 := by
  apply
    exists_odd_prime_ne_one_of_log_ratio_character_budget χ hquad h2 hGRH (by linarith only [hL])
      (Analysis.nonOne_log_ratio_of_ge_22920 hL) hlogq (C := 117 / 10)
  · exact
      (PaperStatements.gamma_primitiveCharacter_sum_re_lt_principal_euler hq χ hne hGRH
          (by nlinarith only [hL, sq_nonneg (L - 22920)])).le
  · linarith only [hL]

end PseudoPrime.LLS
