/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticTripleMain
public import PseudoPrime.LLS.GammaSignedVariationPrincipalBounds

/-! # Principal Gamma sum under the Riemann hypothesis -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under the Riemann hypothesis, the normalized principal exponential sum
satisfies the level-one signed-variation bound at every scale at least one.
Identify its terms with the real parts of the principal Gamma kernel and
transfer the existing bound through the convergent sum. -/
theorem gamma_principal_upper_rh (hRH : RiemannHypothesis) {x : ℝ} (hx : 1 ≤ x) :
    (∑' n : ℕ, Real.exp (-(n : ℝ) / x) * ArithmeticFunction.vonMangoldt n / Real.sqrt x) ≤
      Real.sqrt x +
        (Real.sqrt x / 20 + (5517 / 4000 : ℝ) * Real.log x + 2469 / 800) / Real.sqrt x := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num only) hx
  have h1 : (1 : DirichletCharacter ℂ 1).IsQuadratic := fun z ↦
    Or.inr (Or.inl (MulChar.one_apply (isUnit_of_subsingleton z)))
  have hs :=
    LLS.PaperStatements.MellinKernel.summable_summand LLS.PaperStatements.gammaMellinKernel
      (1 : DirichletCharacter ℂ 1) hx0
  have he (n : ℕ) :
    (LLS.PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x n).re =
      Real.exp (-(n : ℝ) / x) * ArithmeticFunction.vonMangoldt n / Real.sqrt x := by
    rw [LLS.PaperStatements.gamma_quadratic_summand_re_eq_exponential_all _ h1 hx0,
      MulChar.one_apply (isUnit_of_subsingleton (n : ZMod 1)), Complex.one_re, one_mul]
  have ht := LLS.gamma_level_one_sum_upper_signed_variation hRH hx
  have hsum := Complex.reCLM.map_tsum hs
  change
    (∑' n : ℕ, LLS.PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x n).re =
      ∑' n : ℕ,
        (LLS.PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x n).re at hsum
  rw [hsum, tsum_congr he] at ht
  exact ht

/-- Rational lower and upper square-root bounds and an upper logarithm bound
turn the principal signed-variation estimate into an explicit scalar cap.
The positive lower root controls the denominator of the correction term. -/
theorem gamma_principal_upper_rh_cap (hRH : RiemannHypothesis) {x R T Z U : ℝ} (hx : 1 ≤ x)
    (hR : 0 < R) (hrlo : R ≤ Real.sqrt x) (hrhi : Real.sqrt x ≤ T) (hlog : Real.log x ≤ Z)
    (hnum : 0 ≤ (5517 / 4000 : ℝ) * Z + 2469 / 800)
    (hcap : T + 1 / 20 + ((5517 / 4000 : ℝ) * Z + 2469 / 800) / R ≤ U) :
    (∑' n : ℕ, Real.exp (-(n : ℝ) / x) * ArithmeticFunction.vonMangoldt n / Real.sqrt x) ≤ U := by
  have hs : 0 < Real.sqrt x := lt_of_lt_of_le hR hrlo
  have hn : (5517 / 4000 : ℝ) * Real.log x + 2469 / 800 ≤ (5517 / 4000 : ℝ) * Z + 2469 / 800 := by
    linarith only [hlog]
  have hdiv := div_le_div_of_nonneg_right hn hs.le
  rw [add_div] at hdiv
  have hden := div_le_div_of_nonneg_left hnum hR hrlo
  have heq : Real.sqrt x / 20 / Real.sqrt x = (1 / 20 : ℝ) := by
    apply (div_eq_iff (ne_of_gt hs)).2
    ring
  have h := gamma_principal_upper_rh hRH hx
  rw [add_div, add_div, heq] at h
  linarith only [h, hdiv, hden, hrhi, hcap]

end PseudoPrime.PrimeTestBounds.MillerRabin
