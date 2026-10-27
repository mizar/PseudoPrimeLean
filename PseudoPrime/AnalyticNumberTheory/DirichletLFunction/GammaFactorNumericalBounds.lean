/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GammaFactorVerticalGrowth
public import PseudoPrime.AnalyticNumberTheory.Gamma.NumericalDigammaBounds

/-! # Numerical bounds for real gamma-factor logarithmic derivatives

Both character parities reduce to real Gamma arguments in the interval [1/2,17/4].
The resulting constant six controls the archimedean part of centered Poisson estimates.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- For real sigma in [1,17/2], the real logarithmic derivative of GammaReal has
absolute value at most six. The explicit digamma formula reduces it to the real
Gamma argument sigma/2 in [1/2,17/4]. This supplies the fixed archimedean error. -/
theorem abs_re_logDeriv_GammaReal_le_six {σ : ℝ} (hσ : 1 ≤ σ) (hσu : σ ≤ 17 / 2) :
    |(logDeriv Complex.Gammaℝ (σ : ℂ)).re| ≤ 6 := by
  have hp : 0 < (σ : ℂ).re := lt_of_lt_of_le zero_lt_one hσ
  have hr : ∀ m : ℕ, (σ : ℂ) / 2 ≠ -(m : ℂ) := by
    simpa only [Complex.ofReal_zero, add_zero] using
      half_add_ne_neg_nat_of_re_pos hp (a := 0) le_rfl
  have hb :=
    Gamma.abs_real_digamma_sub_log_pi_div_two_le_six (r := σ / 2) (by linarith only [hσ])
      (by linarith only [hσu])
  rw [logDeriv_Gammaℝ_of_half_ne_neg_nat hr]
  rw [show (σ : ℂ) / 2 = ((σ / 2 : ℝ) : ℂ) from (Complex.ofReal_div σ 2).symm]
  simp only [Complex.add_re, Complex.div_ofNat_re, Complex.neg_re, Complex.log_re,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  simpa only [sub_eq_add_neg, add_div, neg_div, add_comm] using hb

/-- For any character and real sigma in [1,15/2], the real gamma-factor logarithmic
derivative has absolute value at most six. Even characters use GammaReal at sigma;
odd characters use sigma+1. Both lie in the certified interval, independently of the modulus.
This bound is used in real Poisson estimates for the completed L-function. -/
theorem abs_re_logDeriv_gammaFactor_le_six {q : ℕ} (χ : DirichletCharacter ℂ q) {σ : ℝ} (hσ : 1 ≤ σ)
    (hσu : σ ≤ 15 / 2) : |(logDeriv χ.gammaFactor (σ : ℂ)).re| ≤ 6 := by
  have hp : 0 < (σ : ℂ).re := lt_of_lt_of_le zero_lt_one hσ
  have hfun : (1 : DirichletCharacter ℂ 1).gammaFactor = Complex.Gammaℝ := by
    funext z
    exact principal_modulus_one_even.gammaFactor_def z
  rcases logDeriv_gammaFactor_eq_one_or_one_shift χ hp with he | he
  · rw [he, hfun]
    exact abs_re_logDeriv_GammaReal_le_six hσ (by linarith only [hσu])
  · rw [he, hfun]
    rw [show (σ : ℂ) + 1 = ((σ + 1 : ℝ) : ℂ) from (Complex.ofReal_add σ 1).symm]
    exact abs_re_logDeriv_GammaReal_le_six (by linarith only [hσ]) (by linarith only [hσu])

/-- For real sigma in [1,17/2], the real logarithmic derivative of GammaReal has
absolute value at most 8/5. The explicit digamma formula reduces it to the real
Gamma argument sigma/2 in [1/2,17/4]. This supplies the fixed archimedean error. -/
theorem abs_re_logDeriv_GammaReal_le_eight_fifths {σ : ℝ} (hσ : 1 ≤ σ) (hσu : σ ≤ 17 / 2) :
    |(logDeriv Complex.Gammaℝ (σ : ℂ)).re| ≤ 8 / 5 := by
  have hp : 0 < (σ : ℂ).re := lt_of_lt_of_le zero_lt_one hσ
  have hr : ∀ m : ℕ, (σ : ℂ) / 2 ≠ -(m : ℂ) := by
    simpa only [Complex.ofReal_zero, add_zero] using
      half_add_ne_neg_nat_of_re_pos hp (a := 0) le_rfl
  have hb :=
    Gamma.abs_real_digamma_sub_log_pi_div_two_le_eight_fifths (r := σ / 2) (by linarith only [hσ])
      (by linarith only [hσu])
  rw [logDeriv_Gammaℝ_of_half_ne_neg_nat hr]
  rw [show (σ : ℂ) / 2 = ((σ / 2 : ℝ) : ℂ) from (Complex.ofReal_div σ 2).symm]
  simp only [Complex.add_re, Complex.div_ofNat_re, Complex.neg_re, Complex.log_re,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  simpa only [sub_eq_add_neg, add_div, neg_div, add_comm] using hb

/-- For any character and real sigma in [1,15/2], the real gamma-factor logarithmic
derivative has absolute value at most 8/5. Even characters use GammaReal at sigma;
odd characters use sigma+1. Both lie in the certified interval, independently of the modulus.
This bound is used in real Poisson estimates for the completed L-function. -/
theorem abs_re_logDeriv_gammaFactor_le_eight_fifths {q : ℕ} (χ : DirichletCharacter ℂ q) {σ : ℝ}
    (hσ : 1 ≤ σ) (hσu : σ ≤ 15 / 2) : |(logDeriv χ.gammaFactor (σ : ℂ)).re| ≤ 8 / 5 := by
  have hp : 0 < (σ : ℂ).re := lt_of_lt_of_le zero_lt_one hσ
  have hfun : (1 : DirichletCharacter ℂ 1).gammaFactor = Complex.Gammaℝ := by
    funext z
    exact principal_modulus_one_even.gammaFactor_def z
  rcases logDeriv_gammaFactor_eq_one_or_one_shift χ hp with he | he
  · rw [he, hfun]
    exact abs_re_logDeriv_GammaReal_le_eight_fifths hσ (by linarith only [hσu])
  · rw [he, hfun]
    rw [show (σ : ℂ) + 1 = ((σ + 1 : ℝ) : ℂ) from (Complex.ofReal_add σ 1).symm]
    exact abs_re_logDeriv_GammaReal_le_eight_fifths (by linarith only [hσ]) (by linarith only [hσu])

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
