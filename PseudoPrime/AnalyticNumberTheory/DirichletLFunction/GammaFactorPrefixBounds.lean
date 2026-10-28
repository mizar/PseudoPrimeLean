/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Gamma.DigammaPrefixBounds
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GammaFactorNumericalBounds
public import PseudoPrime.AnalyticNumberTheory.Gamma.GammaFactorPrefixBounds

/-! # Finite-prefix Gamma-factor allowances

A lower real Gamma argument and a reciprocal-prefix length determine the explicit bound.
Both parity shifts retain the same allowance at each resolvent node.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- For real sigma in [1,17/2] and 1/2≤R≤sigma/2, the GammaReal real logarithmic
 derivative is bounded by the explicit m-term prefix allowance at R.
 Use the exact digamma formula and the certified real prefix bounds.
 This retains the node-dependent lower Gamma argument. -/
theorem abs_re_logDeriv_GammaReal_le_prefix {σ : ℝ} (hσ : 1 ≤ σ) (hσu : σ ≤ 17 / 2) {R : ℝ}
    (hR : 1 / 2 ≤ R) (hRσ : R ≤ σ / 2) (m : ℕ) :
    |(logDeriv Complex.Gammaℝ (σ : ℂ)).re| ≤ Gamma.gammaPrefixAllowance R m := by
  have hp : 0 < (σ : ℂ).re := by
    change 0 < σ
    linarith only [hσ]
  have hr : ∀ m : ℕ, (σ : ℂ) / 2 ≠ -(m : ℂ) := by
    simpa only [Complex.ofReal_zero, add_zero] using
      half_add_ne_neg_nat_of_re_pos hp (a := 0) le_rfl
  have hb :=
    Gamma.real_archimedean_correction_bound_of_prefix hR hRσ
      (show σ / 2 ≤ 17 / 4 by linarith only [hσu]) m
  rw [logDeriv_Gammaℝ_of_half_ne_neg_nat hr]
  rw [show (σ : ℂ) / 2 = ((σ / 2 : ℝ) : ℂ) from (Complex.ofReal_div σ 2).symm]
  simp only [Complex.add_re, Complex.div_ofNat_re, Complex.neg_re, Complex.log_re,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  simpa only [Gamma.gammaPrefixAllowance, sub_eq_add_neg, add_div, neg_div, add_comm] using hb

/-- For a Dirichlet character, sigma in [1,15/2] and 1/2≤R≤sigma/2,
 the real Gamma-factor logarithmic derivative is bounded by the m-term allowance at R.
 Both parity shifts have argument at least R. This supplies the node-specific Poisson error. -/
theorem abs_re_logDeriv_gammaFactor_le_prefix {q : ℕ} (χ : DirichletCharacter ℂ q) {σ : ℝ}
    (hσ : 1 ≤ σ) (hσu : σ ≤ 15 / 2) {R : ℝ} (hR : 1 / 2 ≤ R) (hRσ : R ≤ σ / 2) (m : ℕ) :
    |(logDeriv χ.gammaFactor (σ : ℂ)).re| ≤ Gamma.gammaPrefixAllowance R m := by
  have hp : 0 < (σ : ℂ).re := by
    change 0 < σ
    linarith only [hσ]
  have hfun : (1 : DirichletCharacter ℂ 1).gammaFactor = Complex.Gammaℝ := by
    funext z
    exact principal_modulus_one_even.gammaFactor_def z
  rcases logDeriv_gammaFactor_eq_one_or_one_shift χ hp with he | he
  · rw [he, hfun]
    exact abs_re_logDeriv_GammaReal_le_prefix hσ (by linarith only [hσu]) hR hRσ m
  · rw [he, hfun]
    rw [show (σ : ℂ) + 1 = ((σ + 1 : ℝ) : ℂ) from (Complex.ofReal_add σ 1).symm]
    exact
      abs_re_logDeriv_GammaReal_le_prefix (by linarith only [hσ]) (by linarith only [hσu]) hR
        (by linarith only [hRσ]) m

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
