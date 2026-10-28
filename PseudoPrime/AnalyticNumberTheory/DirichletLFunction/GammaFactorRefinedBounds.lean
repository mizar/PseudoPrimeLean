/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PoissonNumericalBounds
public import PseudoPrime.AnalyticNumberTheory.Gamma.GammaFactorRefinedBounds

/-! # Sharper real archimedean corrections away from the first Gamma argument

Digamma monotonicity improves the correction to 9/10 when the argument is at least one.
The parity-dependent Dirichlet Gamma factors preserve the same bound for sigma at least two.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- For real sigma 2≤sigma≤17/2, the GammaReal logarithmic derivative has real part
 of absolute value at most 9/10. Use its exact digamma formula at sigma/2.
 This transfers the sharper endpoint bound to the completed Gamma factor. -/
theorem abs_re_logDeriv_GammaReal_le_nine_tenths {σ : ℝ} (hσ : 2 ≤ σ) (hσu : σ ≤ 17 / 2) :
    |(logDeriv Complex.Gammaℝ (σ : ℂ)).re| ≤ 9 / 10 := by
  have hp : 0 < (σ : ℂ).re := by
    change 0 < σ
    linarith only [hσ]
  have hr : ∀ m : ℕ, (σ : ℂ) / 2 ≠ -(m : ℂ) := by
    simpa only [Complex.ofReal_zero, add_zero] using
      half_add_ne_neg_nat_of_re_pos hp (a := 0) le_rfl
  have hb :=
    Gamma.abs_real_digamma_sub_log_pi_div_two_le_nine_tenths (r := σ / 2) (by linarith only [hσ])
      (by linarith only [hσu])
  rw [logDeriv_Gammaℝ_of_half_ne_neg_nat hr]
  rw [show (σ : ℂ) / 2 = ((σ / 2 : ℝ) : ℂ) from (Complex.ofReal_div σ 2).symm]
  simp only [Complex.add_re, Complex.div_ofNat_re, Complex.neg_re, Complex.log_re,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  simpa only [sub_eq_add_neg, add_div, neg_div, add_comm] using hb

/-- For any Dirichlet character and real sigma in [2,15/2], its Gamma-factor logarithmic
 derivative has real part of absolute value at most 9/10. Treat both parity shifts explicitly.
 This supplies the improved centered Poisson error for later resolvent nodes. -/
theorem abs_re_logDeriv_gammaFactor_le_nine_tenths {q : ℕ} (χ : DirichletCharacter ℂ q) {σ : ℝ}
    (hσ : 2 ≤ σ) (hσu : σ ≤ 15 / 2) : |(logDeriv χ.gammaFactor (σ : ℂ)).re| ≤ 9 / 10 := by
  have hp : 0 < (σ : ℂ).re := by
    change 0 < σ
    linarith only [hσ]
  have hfun : (1 : DirichletCharacter ℂ 1).gammaFactor = Complex.Gammaℝ := by
    funext z
    exact principal_modulus_one_even.gammaFactor_def z
  rcases logDeriv_gammaFactor_eq_one_or_one_shift χ hp with he | he
  · rw [he, hfun]
    exact abs_re_logDeriv_GammaReal_le_nine_tenths hσ (by linarith only [hσu])
  · rw [he, hfun]
    rw [show (σ : ℂ) + 1 = ((σ + 1 : ℝ) : ℂ) from (Complex.ofReal_add σ 1).symm]
    exact abs_re_logDeriv_GammaReal_le_nine_tenths (by linarith only [hσ]) (by linarith only [hσu])

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
