/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannXi.LogDerivGammaFactor
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.Basic

/-! # Vertical regularity and logarithmic growth of the xi logarithmic derivative

The Euler series, gamma-factor bound and elementary poles control right lines.
Reflection through the xi functional equation controls left lines.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannXi

/-- On a fixed line with real part in `(1,2]`, the ξ logarithmic derivative has a
positive full-line logarithmic majorant. Bound zeta by the absolute Mangoldt series,
gamma by its vertical estimate, and both poles by their real-part distances.
This supplies an integrable Mellin majorant without RH. -/
theorem exists_norm_logDeriv_vertical_right_le_log {σ : ℝ} (hσ : 1 < σ) (hσ' : σ ≤ 2) :
    ∃ A : ℝ,
      0 < A ∧
        ∀ t : ℝ, ‖logDeriv riemannXi ((σ : ℂ) + Complex.I * t)‖ ≤ A * (Real.log (4 + |t|) + 1) := by
  obtain ⟨B, hB, hb⟩ :=
    DirichletLFunction.exists_norm_logDeriv_gammaFactor_vertical_le_log (1 : DirichletCharacter ℂ 1)
      (zero_lt_one.trans hσ) hσ'
  let M := ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ σ
  have hM : 0 ≤ M :=
    tsum_nonneg
      (fun n =>
        div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) σ))
  have hσ0 : 0 < σ := zero_lt_one.trans hσ
  have hσ1 : 0 < σ - 1 := sub_pos.mpr hσ
  let P := 1 / σ + 1 / (σ - 1)
  have hP : 0 ≤ P := add_nonneg (one_div_pos.mpr hσ0).le (one_div_pos.mpr hσ1).le
  refine ⟨B + M + P, add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg hB hM) hP, fun t => ?_⟩
  have hr : 1 < ((σ : ℂ) + Complex.I * t).re := by
    simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero] using hσ
  have ho : ‖logDeriv riemannZeta ((σ : ℂ) + Complex.I * t)‖ ≤ M := by
    have h :=
      DirichletLFunction.norm_neg_deriv_div_dirichletLFunction_le_vonMangoldt_tsum
        (1 : DirichletCharacter ℂ 1) hσ t
    simpa only [DirichletCharacter.LFunction_modOne_eq, neg_div, norm_neg, logDeriv_apply,
      mul_comm] using h
  have hp0 : ‖1 / ((σ : ℂ) + Complex.I * t)‖ ≤ 1 / σ := by
    have hr0 := Complex.re_le_norm ((σ : ℂ) + Complex.I * t)
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero] at hr0
    rw [one_div, norm_inv, ← one_div]
    exact one_div_le_one_div_of_le hσ0 hr0
  have hp1 : ‖1 / (((σ : ℂ) + Complex.I * t) - 1)‖ ≤ 1 / (σ - 1) := by
    have hr1 := Complex.re_le_norm (((σ : ℂ) + Complex.I * t) - 1)
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero,
      Complex.one_re] at hr1
    rw [one_div, norm_inv, ← one_div]
    exact one_div_le_one_div_of_le hσ1 hr1
  rw [logDeriv_eq_poles_gammaFactor_zeta_of_one_lt_re hr]
  have hn0 := norm_add_le (1 / ((σ : ℂ) + Complex.I * t)) (1 / (((σ : ℂ) + Complex.I * t) - 1))
  have hn1 :=
    norm_add_le (1 / ((σ : ℂ) + Complex.I * t) + 1 / (((σ : ℂ) + Complex.I * t) - 1))
      (logDeriv (1 : DirichletCharacter ℂ 1).gammaFactor ((σ : ℂ) + Complex.I * t))
  have hn2 :=
    norm_add_le
      (1 / ((σ : ℂ) + Complex.I * t) + 1 / (((σ : ℂ) + Complex.I * t) - 1) +
        logDeriv (1 : DirichletCharacter ℂ 1).gammaFactor ((σ : ℂ) + Complex.I * t))
      (logDeriv riemannZeta ((σ : ℂ) + Complex.I * t))
  have hL : 0 ≤ Real.log (4 + |t|) := Real.log_nonneg (by linarith only [abs_nonneg t])
  dsimp only [P] at hP ⊢
  nlinarith only [hn0, hn1, hn2, hp0, hp1, ho, hb t, hL, hM, hP]

/-- On a fixed line with real part in `[-1,0)`, the ξ logarithmic derivative has a
positive full-line logarithmic majorant. Reflect to the right line at `1-σ` and
reverse the imaginary parameter. This supplies the left Mellin majorant without RH. -/
theorem exists_norm_logDeriv_vertical_left_le_log {σ : ℝ} (hσ : σ < 0) (hσ' : -1 ≤ σ) :
    ∃ A : ℝ,
      0 < A ∧
        ∀ t : ℝ, ‖logDeriv riemannXi ((σ : ℂ) + Complex.I * t)‖ ≤ A * (Real.log (4 + |t|) + 1) := by
  obtain ⟨A, hA, hb⟩ :=
    exists_norm_logDeriv_vertical_right_le_log (σ := 1 - σ) (by linarith only [hσ])
      (by linarith only [hσ'])
  refine ⟨A, hA, fun t => ?_⟩
  have h := hb (-t)
  have he : ((1 - σ : ℝ) : ℂ) + Complex.I * (-t : ℝ) = 1 - ((σ : ℂ) + Complex.I * t) := by
    rw [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_neg]
    ring
  rw [he, logDeriv_one_sub, norm_neg, abs_neg] at h
  exact h

/-- To the right of one, ξ is analytic and nonzero, so its logarithmic derivative
is continuous along the whole vertical line. Compose its analytic quotient with
the line parametrization. This gives measurability for vertical integration. -/
theorem continuous_logDeriv_vertical_right {σ : ℝ} (hσ : 1 < σ) :
    Continuous (fun t : ℝ => logDeriv riemannXi ((σ : ℂ) + Complex.I * t)) := by
  rw [continuous_iff_continuousAt]
  intro t
  have hs : 1 < ((σ : ℂ) + Complex.I * t).re := by
    simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero] using hσ
  have hξ := differentiable_riemannXi.analyticAt ((σ : ℂ) + Complex.I * t)
  have hd : AnalyticAt ℂ (logDeriv riemannXi) ((σ : ℂ) + Complex.I * t) :=
    hξ.deriv.div hξ (riemannXi_ne_zero_of_one_lt_re hs)
  exact
    hd.continuousAt.comp (f := fun t : ℝ => (σ : ℂ) + Complex.I * t)
      ((continuous_const.add (continuous_const.mul Complex.continuous_ofReal)).continuousAt)

/-- On a negative-real-part line, ξ is nonzero by its functional equation and
right-half-plane nonvanishing. Its analytic logarithmic derivative is therefore
continuous on the line. This gives measurability for the reflected Mellin contour. -/
theorem continuous_logDeriv_vertical_left {σ : ℝ} (hσ : σ < 0) :
    Continuous (fun t : ℝ => logDeriv riemannXi ((σ : ℂ) + Complex.I * t)) := by
  rw [continuous_iff_continuousAt]
  intro t
  have hs : 1 < (1 - ((σ : ℂ) + Complex.I * t)).re := by
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero, Complex.one_re]
    linarith only [hσ]
  have hn : riemannXi ((σ : ℂ) + Complex.I * t) ≠ 0 := by
    rw [← riemannXi_one_sub]
    exact riemannXi_ne_zero_of_one_lt_re hs
  have hξ := differentiable_riemannXi.analyticAt ((σ : ℂ) + Complex.I * t)
  have hd : AnalyticAt ℂ (logDeriv riemannXi) ((σ : ℂ) + Complex.I * t) := hξ.deriv.div hξ hn
  exact
    hd.continuousAt.comp (f := fun t : ℝ => (σ : ℂ) + Complex.I * t)
      ((continuous_const.add (continuous_const.mul Complex.continuous_ofReal)).continuousAt)

end PseudoPrime.AnalyticNumberTheory.RiemannXi
