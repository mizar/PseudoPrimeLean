/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaConductorFreeNonOneBounds
public import PseudoPrime.Analysis.LLSGammaNonOneLogRatioBounds

/-! # Non-one Gamma witnesses with explicit logarithmic and prefix budgets -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Under GRH, a nonprincipal quadratic character of even level q ≥ 20000 has an
odd-prime non-one witness at most (4/5)L² whenever L ≥ 29121 and log q ≤ L+7/5.
Apply the parameterized comparison with the existing 32-term prefix certificate.
This improves the starting scale without generating further finite certificates. -/
theorem exists_odd_prime_ne_one_of_gamma_log_29121 {q : ℕ} [NeZero q] (hq : 20000 ≤ q)
    (χ : DirichletCharacter ℂ q) (hquad : χ.IsQuadratic) (hne : χ ≠ 1) (h2 : 2 ∣ q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {L : ℝ} (hL : 29121 ≤ L)
    (hlogq : Real.log q ≤ L + 7 / 5) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ (4 / 5 : ℝ) * L ^ 2 ∧ χ p ≠ 1 := by
  exact
    exists_odd_prime_ne_one_of_log_ratio_prefix_profile hq χ hquad hne h2 hGRH
      (by linarith only [hL]) (Analysis.nonOne_log_ratio_of_ge_29121 hL) hlogq 32
      Analysis.gammaResolvent_thirtyTwo_error_lt (by linarith only [hL])

end PseudoPrime.LLS
