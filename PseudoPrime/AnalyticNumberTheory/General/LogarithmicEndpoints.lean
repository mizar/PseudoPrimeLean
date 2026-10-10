/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.General.ShiftedLogarithmicResidues
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Endpoint integration of logarithmic derivatives and shifted Mellin-pole residues.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.General

/-- If F has complex derivative F' at the real point σ and F(σ) ≠ 0, the real
function `t ↦ log (norm (F t))` has derivative `Re (F' / F(σ))` there.
Differentiate the squared norm and its real logarithm. This gives the local endpoint
integration identity without choosing a branch of the complex logarithm. -/
theorem hasDerivAt_log_norm_of_complex {F : ℂ → ℂ} {F' : ℂ} {σ : ℝ} (hF : HasDerivAt F F' (σ : ℂ))
    (hne : F (σ : ℂ) ≠ 0) :
    HasDerivAt (fun t : ℝ ↦ Real.log ‖F (t : ℂ)‖) (F' / F (σ : ℂ)).re σ := by
  have h :=
    ((hF.comp_ofReal.norm_sq).log (pow_ne_zero 2 (norm_ne_zero_iff.mpr hne))).const_mul (1 / 2 : ℝ)
  have heq :
    (fun t : ℝ ↦ (1 / 2 : ℝ) * Real.log (‖F (t : ℂ)‖ ^ 2)) =
      (fun t : ℝ ↦ Real.log ‖F (t : ℂ)‖) := by
    funext t
    rw [Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    ring
  rw [heq] at h
  have hd : (1 / 2 : ℝ) * (2 * inner ℝ (F (σ : ℂ)) F' / ‖F (σ : ℂ)‖ ^ 2) = (F' / F (σ : ℂ)).re := by
    rw [real_inner_eq_re_inner ℂ, RCLike.inner_apply, RCLike.re_to_complex, Complex.mul_re,
      Complex.conj_re, Complex.conj_im, Complex.div_re, pow_two, Complex.norm_mul_self_eq_normSq]
    ring
  rwa [hd] at h

/-- If F is analytic and nonzero on the real ray starting at one, tends to one at infinity,
and has an integrable logarithmic derivative, its real-part integral equals -log|F(1)|.
Apply the real half-line fundamental theorem of calculus to log|F|. -/
theorem integral_logDeriv_re_eq_neg_log_norm {F : ℂ → ℂ}
    (hF : ∀ σ : ℝ, 1 ≤ σ → AnalyticAt ℂ F (σ : ℂ)) (hne : ∀ σ : ℝ, 1 ≤ σ → F (σ : ℂ) ≠ 0)
    (hlim : Filter.Tendsto (fun σ : ℝ ↦ F (σ : ℂ)) Filter.atTop (nhds 1))
    (hi : MeasureTheory.IntegrableOn (fun σ : ℝ ↦ logDeriv F (σ : ℂ)) (Set.Ioi 1)) :
    (∫ σ : ℝ in Set.Ioi 1, (logDeriv F (σ : ℂ)).re) = -Real.log ‖F 1‖ := by
  have hd :
    ∀ σ ∈ Set.Ici (1 : ℝ),
      HasDerivAt (fun t : ℝ ↦ Real.log ‖F (t : ℂ)‖) (logDeriv F (σ : ℂ)).re σ := by
    intro σ hσ
    exact hasDerivAt_log_norm_of_complex (hF σ hσ).differentiableAt.hasDerivAt (hne σ hσ)
  have ht : Filter.Tendsto (fun σ : ℝ ↦ Real.log ‖F (σ : ℂ)‖) Filter.atTop (nhds 0) := by
    have hone : ‖(1 : ℂ)‖ ≠ 0 := by
      rw [norm_one]; exact one_ne_zero
    have ht0 := (Real.continuousAt_log hone).tendsto.comp hlim.norm
    have ht1 :
      Filter.Tendsto (fun σ : ℝ ↦ Real.log ‖F (σ : ℂ)‖) Filter.atTop (nhds (Real.log ‖(1 : ℂ)‖)) :=
      ht0
    simpa only [norm_one, Real.log_one] using ht1
  have hr : MeasureTheory.IntegrableOn (fun σ : ℝ ↦ (logDeriv F (σ : ℂ)).re) (Set.Ioi 1) :=
    Complex.reCLM.integrable_comp hi
  simpa only [Complex.ofReal_one, zero_sub] using
    MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto' hd hr ht

/-- For an analytic nonzero function on the real ray, a logarithmic derivative tending to zero,
and an integrable derivative, integrating the derivative's real part gives -Re logDeriv F(1).
The half-line fundamental theorem computes the endpoint term of the Mellin residue. -/
theorem integral_deriv_logDeriv_re_eq_neg_endpoint {F : ℂ → ℂ}
    (hF : ∀ σ : ℝ, 1 ≤ σ → AnalyticAt ℂ F (σ : ℂ)) (hne : ∀ σ : ℝ, 1 ≤ σ → F (σ : ℂ) ≠ 0)
    (hlim : Filter.Tendsto (fun σ : ℝ ↦ logDeriv F (σ : ℂ)) Filter.atTop (nhds 0))
    (hi : MeasureTheory.IntegrableOn (fun σ : ℝ ↦ deriv (logDeriv F) (σ : ℂ)) (Set.Ioi 1)) :
    (∫ σ : ℝ in Set.Ioi 1, (deriv (logDeriv F) (σ : ℂ)).re) = -(logDeriv F 1).re := by
  have hd :
    ∀ σ ∈ Set.Ici (1 : ℝ),
      HasDerivAt (fun t : ℝ ↦ (logDeriv F (t : ℂ)).re) (deriv (logDeriv F) (σ : ℂ)).re σ := by
    intro σ hσ
    exact ((hF σ hσ).deriv.div (hF σ hσ) (hne σ hσ)).differentiableAt.hasDerivAt.real_of_complex
  have hr : MeasureTheory.IntegrableOn (fun σ : ℝ ↦ (deriv (logDeriv F) (σ : ℂ)).re) (Set.Ioi 1) :=
    Complex.reCLM.integrable_comp hi
  have ht := Complex.continuous_re.continuousAt.tendsto.comp hlim
  simpa only [Complex.ofReal_one, Complex.zero_re, zero_sub] using
    MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto' hd hr ht

/-- For x > 1, assume F is analytic and nonzero at every real σ ≥ 1, F(σ) tends
to one, and its logarithmic derivative tends to zero at positive infinity.
Assume the logarithmic derivative and its derivative are integrable on σ > 1.
The real shifted-origin residue, integrated over that ray and divided by log x,
equals `log (norm (F 1)) + Re (logDeriv F 1) / log x`.
Combine the two half-line endpoint integrals to evaluate the Mellin origin contribution. -/
theorem integral_shifted_origin_re_div_log {F : ℂ → ℂ} {x : ℝ} (hx : 1 < x)
    (hF : ∀ σ : ℝ, 1 ≤ σ → AnalyticAt ℂ F (σ : ℂ)) (hne : ∀ σ : ℝ, 1 ≤ σ → F (σ : ℂ) ≠ 0)
    (hlim : Filter.Tendsto (fun σ : ℝ ↦ F (σ : ℂ)) Filter.atTop (nhds 1))
    (hlimD : Filter.Tendsto (fun σ : ℝ ↦ logDeriv F (σ : ℂ)) Filter.atTop (nhds 0))
    (hi : MeasureTheory.IntegrableOn (fun σ : ℝ ↦ logDeriv F (σ : ℂ)) (Set.Ioi 1))
    (hiD : MeasureTheory.IntegrableOn (fun σ : ℝ ↦ deriv (logDeriv F) (σ : ℂ)) (Set.Ioi 1)) :
    (∫ σ : ℝ in Set.Ioi 1,
          (-deriv (logDeriv F) (σ : ℂ) - logDeriv F (σ : ℂ) * (Real.log x : ℂ)).re) /
        Real.log x =
      Real.log ‖F 1‖ + (logDeriv F 1).re / Real.log x := by
  have hr : MeasureTheory.IntegrableOn (fun σ : ℝ ↦ (logDeriv F (σ : ℂ)).re) (Set.Ioi 1) :=
    Complex.reCLM.integrable_comp hi
  have hrD : MeasureTheory.IntegrableOn (fun σ : ℝ ↦ (deriv (logDeriv F) (σ : ℂ)).re) (Set.Ioi 1) :=
    Complex.reCLM.integrable_comp hiD
  simp only [Complex.sub_re, Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]
  have hrDN :
    MeasureTheory.IntegrableOn (fun σ : ℝ ↦ -(deriv (logDeriv F) (σ : ℂ)).re) (Set.Ioi 1) := hrD.neg
  have hrM :
    MeasureTheory.IntegrableOn (fun σ : ℝ ↦ (logDeriv F (σ : ℂ)).re * Real.log x) (Set.Ioi 1) :=
    hr.mul_const _
  rw [MeasureTheory.integral_sub hrDN hrM, MeasureTheory.integral_neg,
    MeasureTheory.integral_mul_const, integral_deriv_logDeriv_re_eq_neg_endpoint hF hne hlimD hiD,
    integral_logDeriv_re_eq_neg_log_norm hF hne hlim hi]
  field_simp [ne_of_gt (Real.log_pos hx)]
  ring

/-- For x > 1, assume F is analytic and nonzero on the real ray σ ≥ 1, tends to one,
and has logarithmic derivative tending to zero. Require both that derivative and its
complex derivative to be integrable on σ > 1. Integrating the real derivative at zero
of the shifted origin regularization and dividing by log x gives
`log (norm (F 1)) + Re (logDeriv F 1) / log x`.
Identify the local regularization derivative and apply the endpoint integral formula;
this connects the origin residue to the logarithmic L-value. -/
theorem integral_origin_regularization_re_div_log {F : ℂ → ℂ} {x : ℝ} (hx : 1 < x)
    (hF : ∀ σ : ℝ, 1 ≤ σ → AnalyticAt ℂ F (σ : ℂ)) (hne : ∀ σ : ℝ, 1 ≤ σ → F (σ : ℂ) ≠ 0)
    (hlim : Filter.Tendsto (fun σ : ℝ ↦ F (σ : ℂ)) Filter.atTop (nhds 1))
    (hlimD : Filter.Tendsto (fun σ : ℝ ↦ logDeriv F (σ : ℂ)) Filter.atTop (nhds 0))
    (hi : MeasureTheory.IntegrableOn (fun σ : ℝ ↦ logDeriv F (σ : ℂ)) (Set.Ioi 1))
    (hiD : MeasureTheory.IntegrableOn (fun σ : ℝ ↦ deriv (logDeriv F) (σ : ℂ)) (Set.Ioi 1)) :
    (∫ σ : ℝ in Set.Ioi 1, (deriv (shiftedLogarithmicRegularization F x (σ : ℂ)) 0).re) /
        Real.log x =
      Real.log ‖F 1‖ + (logDeriv F 1).re / Real.log x := by
  have heq :
    (∫ σ : ℝ in Set.Ioi 1, (deriv (shiftedLogarithmicRegularization F x (σ : ℂ)) 0).re) =
      ∫ σ : ℝ in Set.Ioi 1,
        (-deriv (logDeriv F) (σ : ℂ) - logDeriv F (σ : ℂ) * (Real.log x : ℂ)).re := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro σ hσ
    exact
      congrArg Complex.re
        (deriv_shiftedLogarithmicRegularization (hF σ hσ.le) (hne σ hσ.le) (zero_lt_one.trans hx))
  rw [heq]
  exact integral_shifted_origin_re_div_log hx hF hne hlim hlimD hi hiD

end PseudoPrime.AnalyticNumberTheory.General
