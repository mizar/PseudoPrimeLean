/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaVariablePrefixCharacterBounds
public import PseudoPrime.LLS.GammaNonOneComparison

/-! # Variable-prefix non-one witness interface

A finite certified error sum supplies the actual Gamma arithmetic upper budget.
Prefix length and additive cost are parameters of one common witness comparison.
-/

@[expose] public section

namespace PseudoPrime.LLS

/-- Under GRH, for a nonprincipal quadratic character at even q≥20000 and x≥1,
 any certified prefix error C and strict numerical comparison yield an odd non-one prime.
 Use the common primitive Gamma upper bound and the actual prime-two comparison.
 Only the scalar principal/ramp gap remains to be certified for a chosen starting value;
 the analytic proof is independent of the prefix length. -/
theorem exists_odd_prime_ne_one_of_variable_prefix_budget {q : ℕ} [NeZero q] (hq : 20000 ≤ q)
    (χ : DirichletCharacter ℂ q) (hquad : χ.IsQuadratic) (hne : χ ≠ 1) (h2 : 2 ∣ q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 1 ≤ x)
    (hcut : 1 ≤ (99 / 40 : ℝ) * x) (prefixLen : ℕ) {C : ℝ}
    (hC : Analysis.gammaResolventPrefixErrorSum prefixLen < C)
    (hgap :
      (∑' n : ℕ, PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x n).re +
          ((11783423 / 25000000 : ℝ) * Real.log χ.conductor + C + 64 / 9 +
            ((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x +
            x ^ (-9 / 16 : ℝ) * ((16 / 5) * (Real.log χ.conductor + 283) + 5 / 3)) +
          (Real.log ((99 / 40 : ℝ) * x) + Real.log 2) / Real.sqrt x <
        2 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x)) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ χ p ≠ 1 := by
  have hnp :=
    PaperStatements.gamma_primitiveCharacter_sum_re_le_variable_prefix_scale hq χ hne hGRH hx
      prefixLen hC
  apply exists_odd_prime_ne_one_of_gamma_ramp_gap χ hquad h2 (zero_lt_one.trans_le hx) hcut
  linarith only [hnp, hgap]

end PseudoPrime.LLS
