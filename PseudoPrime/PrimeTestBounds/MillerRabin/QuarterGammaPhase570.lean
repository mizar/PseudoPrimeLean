/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCentralGamma570
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028GammaConvolution

/-! # Real Gamma phase and pole convolution for the section 31 kernel -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Real oscillatory factor of the section 31 kernel at logarithmic scale y. -/
noncomputable def gammaPhase570 (y t : ℝ) : ℝ :=
  (quarterKernel570.function (Complex.I * t) * Complex.exp (Complex.I * (t : ℂ) * y)).re

/-- For an even character, the sum of the reflected and right central
Gamma integrands equals the real digamma factor times the complex kernel phase. -/
theorem even_gamma_integrand_eq_570 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (he : χ.Even)
    (x t : ℝ) :
    reflectedGammaIntegrand570 χ⁻¹ x ((0 : ℂ) + t * Complex.I) +
        gammaIntegrand570 χ x ((0 : ℂ) + t * Complex.I) =
      (((Complex.digamma (((1 / 4 : ℝ) : ℂ) + Complex.I * (t / 2 : ℝ))).re - Real.log Real.pi : ℝ) :
          ℂ) *
        (quarterKernel570.function (Complex.I * t) * (x : ℂ) ^ (Complex.I * t)) := by
  have heinv : χ⁻¹.Even := AnalyticNumberTheory.DirichletLFunction.character_even_inv_iff.mpr he
  have hγ : χ⁻¹.gammaFactor = χ.gammaFactor := by
    funext z
    rw [heinv.gammaFactor_def, he.gammaFactor_def]
  have hs : star (Complex.I * (t : ℂ) + 1 / 2) = 1 / 2 - Complex.I * t := by
    simp only [Complex.star_def, map_add, map_mul, Complex.conj_I, Complex.conj_ofReal, map_div₀,
      map_one, map_ofNat]
    ring
  have hd := refined_even_gamma_real_digamma χ he t
  unfold reflectedGammaIntegrand570 gammaIntegrand570
  simp only [zero_add, mul_comm (t : ℂ) Complex.I, hγ]
  rw [← hs, refined_even_gamma_logDeriv_conj χ he, ← hd]
  have heq :
    star (logDeriv χ.gammaFactor (Complex.I * (t : ℂ) + 1 / 2)) +
        logDeriv χ.gammaFactor (Complex.I * (t : ℂ) + 1 / 2) =
      (((2 : ℝ) * (logDeriv χ.gammaFactor (Complex.I * (t : ℂ) + 1 / 2)).re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp only [Complex.add_re, Complex.star_def, Complex.conj_re, Complex.ofReal_re]
      ring
    · simp only [Complex.add_im, Complex.star_def, Complex.conj_im, Complex.ofReal_im]
      ring
  rw [← heq]
  ring

/-- For an even character and positive x, the real central integral is the
normalized integral of the real digamma weight against the section 31 phase.
Absolute integrability permits commuting the real part with the integral. -/
theorem central_real_phase_570 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (he : χ.Even) {x : ℝ}
    (hx : 0 < x) :
    let f := fun t : ℝ ↦
      ((Complex.digamma ((1 / 4 : ℂ) + Complex.I * (t / 2 : ℝ))).re - Real.log Real.pi) *
        gammaPhase570 (Real.log x) t
    MeasureTheory.Integrable f ∧ (centralGammaPair570 χ x).re = (∫ t : ℝ, f t) / (2 * Real.pi) := by
  let P := gammaPhase570 (Real.log x)
  let F : ℝ → ℂ := fun t ↦
    reflectedGammaIntegrand570 χ⁻¹ x ((0 : ℂ) + t * Complex.I) +
      gammaIntegrand570 χ x ((0 : ℂ) + t * Complex.I)
  have hi1 :
    MeasureTheory.Integrable
      (fun t : ℝ ↦ reflectedGammaIntegrand570 χ⁻¹ x ((0 : ℂ) + t * Complex.I)) := by
    simpa only [reflectedGammaIntegrand570, mul_comm Complex.I, Complex.ofReal_zero] using
      (reflected_gamma_line_integrable_570 χ⁻¹ (c := 0) hx (by norm_num only) (by norm_num only)
        (by norm_num only))
  have hi2 :
    MeasureTheory.Integrable (fun t : ℝ ↦ gammaIntegrand570 χ x ((0 : ℂ) + t * Complex.I)) := by
    simpa only [gammaIntegrand570, mul_comm Complex.I, Complex.ofReal_zero] using
      (gamma_line_integrable_570 χ (c := 0) hx (by norm_num only) (by norm_num only))
  have hFi : MeasureTheory.Integrable F := hi1.add hi2
  have hp (t : ℝ) : (x : ℂ) ^ (Complex.I * t) = Complex.exp (Complex.I * (t : ℂ) * Real.log x) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'), ← Complex.ofReal_log hx.le]
    congr 1
    ring
  have hpoint (t : ℝ) :
    (F t).re =
      ((Complex.digamma ((1 / 4 : ℂ) + Complex.I * (t / 2 : ℝ))).re - Real.log Real.pi) * P t := by
    dsimp only [F, P, gammaPhase570]
    rw [even_gamma_integrand_eq_570 χ he x t, hp]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  have hG :
    MeasureTheory.Integrable
      (fun t : ℝ ↦
        ((Complex.digamma ((1 / 4 : ℂ) + Complex.I * (t / 2 : ℝ))).re - Real.log Real.pi) *
          P t) := by
    exact hFi.re.congr (Filter.Eventually.of_forall hpoint)
  have hr := Complex.reCLM.integral_comp_comm hFi
  change (∫ t : ℝ, (F t).re) = (∫ t : ℝ, F t).re at hr
  have hint :
    (∫ t : ℝ, (F t).re) =
      ∫ t : ℝ,
        ((Complex.digamma ((1 / 4 : ℂ) + Complex.I * (t / 2 : ℝ))).re - Real.log Real.pi) * P t :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpoint)
  have hpair :
    (centralGammaPair570 χ x).re =
      (∫ t : ℝ,
          ((Complex.digamma ((1 / 4 : ℂ) + Complex.I * (t / 2 : ℝ))).re - Real.log Real.pi) * P t) /
        (2 * Real.pi) := by
    rw [← central_gamma_pair_eq_570 χ he hx, ← mul_add, ← MeasureTheory.integral_add hi1 hi2]
    change ((((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ, F t)).re = _
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [← hr, hint]
    ring
  exact ⟨hG, hpair⟩

/-- The actual admissible function equals the paper's sixth-pole function
with the exact normalization factor `(27/25)^5`. Rewrite the general
shifted-power identity and evaluate the rational parameters. -/
theorem phase_kernel_function_570 (z : ℂ) :
    quarterKernel570.function z =
      ((51 / 50 : ℂ) ^ 5) * (Complex.exp ((14 / 5 : ℂ) * z) / (z + 51 / 50) ^ 6) := by
  change Analysis.rationalPoleFunction 3 (25 / 51) (7 / 5) z = _
  rw [Analysis.rationalPole_eq_shifted_power 3 (by norm_num only) (7 / 5) z]
  norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat, Nat.reduceMul]

/-- On every positive input and every line to the right of the sixth pole,
the inverse Mellin transform is the explicit nonnegative rational-pole
profile. This specializes the existing inversion theorem to the refined
parameters without changing its normalization. -/
theorem phase_kernel_inversion_570 {σ u : ℝ} (hσ : 0 < σ + 51 / 50) (hu : 0 < u) :
    Analysis.inverseMellin (quarterKernel570.function) σ u =
      (Analysis.rationalPoleProfile 3 (25 / 51) (7 / 5) u : ℂ) := by
  change Analysis.inverseMellin (Analysis.rationalPoleFunction 3 (25 / 51) (7 / 5)) σ u = _
  apply Analysis.inverseMellin_rationalPole (m := 3) (by norm_num only) (by norm_num only) _ hu
  norm_num only at hσ ⊢
  exact hσ

/-- The Fourier transform of the sixth-pole kernel is its inverse Mellin
profile at `exp (-y)`, with the exact Fourier normalization. This identity
also supplies the profile inside the scaled resolvent convolution. -/
theorem kernel_fourier_eq_570 (y : ℝ) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          quarterKernel570.function (Complex.I * t) * Complex.exp (Complex.I * (t : ℂ) * y)) =
      (Analysis.rationalPoleProfile 3 (25 / 51) (7 / 5) (Real.exp (-y)) : ℂ) := by
  have hu : 0 < Real.exp (-y) := Real.exp_pos _
  have hinv := phase_kernel_inversion_570 (σ := 0) (u := Real.exp (-y)) (by norm_num only) hu
  have hphase (t : ℝ) :
    (Real.exp (-y) : ℂ) ^ (-(Complex.I * t)) = Complex.exp (Complex.I * (t : ℂ) * y) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hu.ne'), ← Complex.ofReal_log hu.le]
    rw [Real.log_exp, Complex.ofReal_neg]
    congr 1
    ring
  unfold Analysis.inverseMellin at hinv
  simpa only [Complex.ofReal_zero, zero_add, hphase] using hinv

/-- The sixth-pole kernel is continuous on the imaginary axis, which stays
strictly to the right of its unique pole. This permits the product Fubini
estimate to be applied to the actual Gamma kernel. -/
theorem kernel_line_continuous_570 :
    Continuous (fun t : ℝ ↦ quarterKernel570.function (Complex.I * t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hden : Complex.I * (t : ℂ) + 51 / 50 ≠ 0 := by
    intro h
    have h27 : (51 / 50 : ℂ) = (((51 / 50 : ℝ)) : ℂ) := by
      push_cast
      ring
    rw [h27] at h
    have hr := congrArg Complex.re h
    norm_num only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, Complex.zero_re] at hr
  have he :
    (fun t : ℝ ↦ quarterKernel570.function (Complex.I * t)) = fun t : ℝ ↦
      ((51 / 50 : ℂ) ^ 5) *
        (Complex.exp ((14 / 5 : ℂ) * (Complex.I * t)) / (Complex.I * t + 51 / 50) ^ 6) := by
    funext t
    exact phase_kernel_function_570 (Complex.I * t)
  rw [he]
  fun_prop (disch := exact pow_ne_zero 6 hden)

/-- The sixth-pole kernel multiplied by a real Fourier phase remains
continuous and integrable. The phase has unit norm, so the Mellin-kernel
integrability estimate applies at every shift. -/
theorem kernel_phase_regular_570 (y : ℝ) :
    Continuous
        (fun t : ℝ ↦
          quarterKernel570.function (Complex.I * t) * Complex.exp (Complex.I * (t : ℂ) * y)) ∧
      MeasureTheory.Integrable
        (fun t : ℝ ↦
          quarterKernel570.function (Complex.I * t) * Complex.exp (Complex.I * (t : ℂ) * y)) := by
  have hp : Continuous (fun t : ℝ ↦ Complex.exp (Complex.I * (t : ℂ) * y)) :=
    Complex.continuous_exp.comp
      ((continuous_const.mul Complex.continuous_ofReal).mul continuous_const)
  constructor
  · exact kernel_line_continuous_570.mul hp
  · have hk :=
      LLS.PaperStatements.MellinKernel.integrable_line quarterKernel570 (c := 0) (by norm_num only)
        (by linarith only [quarterKernel570.delta_pos])
    have hk' :
      MeasureTheory.Integrable (fun t : ℝ ↦ quarterKernel570.function (Complex.I * t)) := by
      simpa only [Complex.ofReal_zero, zero_add] using hk
    apply hk'.mul_bdd (c := 1) hp.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro t
    rw [Complex.norm_exp]
    have hre : (Complex.I * (t : ℂ) * y).re = 0 := by
      simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, mul_zero, sub_zero, one_mul, zero_add]
    rw [hre, Real.exp_zero]

/-- The normalized resolvent integral of the shifted sixth-pole kernel is the
exponential convolution of its inverse Mellin profile. This exact identity
holds at every real resolvent scale and is the starting point for estimating
individual terms of the even-Gamma expansion. -/
theorem kernel_resolvent_convolution_570 (y s : ℝ) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          (quarterKernel570.function (Complex.I * t) * Complex.exp (Complex.I * (t : ℂ) * y)) *
            ((4 : ℂ) / (4 + ((s * t : ℝ) : ℂ) ^ 2))) =
      ∫ v : ℝ,
        (Analysis.rationalPoleProfile 3 (25 / 51) (7 / 5) (Real.exp (-(y + s * v))) : ℂ) *
          (Analysis.ExponentialMeanSquare.weight v : ℂ) := by
  let F : ℝ → ℂ := fun t ↦
    quarterKernel570.function (Complex.I * t) * Complex.exp (Complex.I * (t : ℂ) * y)
  have hf : Continuous F := (kernel_phase_regular_570 y).1
  have hi : MeasureTheory.Integrable F := (kernel_phase_regular_570 y).2
  rw [Analysis.exponential_fourier_resolvent_convolution F hf hi s, ←
    MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_congr_ae
  apply Filter.Eventually.of_forall
  intro v
  dsimp only
  have he :
    (∫ t : ℝ, F t * Complex.exp (Complex.I * (s * (t : ℂ)) * v)) =
      ∫ t : ℝ,
        quarterKernel570.function (Complex.I * t) *
          Complex.exp (Complex.I * (t : ℂ) * (y + s * v : ℝ)) := by
    apply MeasureTheory.integral_congr_ae
    apply Filter.Eventually.of_forall
    intro t
    dsimp only [F]
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [← mul_assoc, he, kernel_fourier_eq_570]

/-- For a positive pole parameter, rescale the sixth-pole convolution so
that its exponential kernel has decay rate `c`. The prefactor is the exact
Jacobian `c / 2`. -/
theorem kernel_resolvent_pole_570 (y : ℝ) {c : ℝ} (hc : 0 < c) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          (quarterKernel570.function (Complex.I * t) * Complex.exp (Complex.I * (t : ℂ) * y)) *
            ((4 : ℂ) / (4 + (((2 / c) * t : ℝ) : ℂ) ^ 2))) =
      ((c / 2 : ℝ) : ℂ) *
        ∫ w : ℝ,
          (Analysis.rationalPoleProfile 3 (25 / 51) (7 / 5) (Real.exp (-(y + w))) : ℂ) *
            (Real.exp (-c * |w|) : ℂ) := by
  rw [kernel_resolvent_convolution_570 y (2 / c)]
  let g : ℝ → ℂ := fun w ↦
    (Analysis.rationalPoleProfile 3 (25 / 51) (7 / 5) (Real.exp (-(y + w))) : ℂ)
  have hs : 0 < 2 / c := div_pos (by norm_num only) hc
  have h := Analysis.exponential_convolution_rescale g hs
  have he : 2 / (2 / c) = c := by
    rw [div_div_eq_mul_div, mul_div_cancel_left₀ c (by norm_num only : (2 : ℝ) ≠ 0)]
  have hi : (2 / c)⁻¹ = c / 2 := by rw [inv_div]
  simpa only [g, he, ← Complex.ofReal_inv, hi] using h

/-- The usual resolvent at a positive pole has the same profile convolution
after multiplying its Fourier integral by `c²`. This exact form keeps the
normalization explicit for the even-Gamma partial fractions. -/
theorem kernel_pole_convolution_570 (y : ℝ) {c : ℝ} (hc : 0 < c) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * ((c ^ 2 : ℝ) : ℂ) *
        (∫ t : ℝ,
          (quarterKernel570.function (Complex.I * t) * Complex.exp (Complex.I * (t : ℂ) * y)) *
            ((1 / (c ^ 2 + t ^ 2) : ℝ) : ℂ)) =
      ((c / 2 : ℝ) : ℂ) *
        ∫ w : ℝ,
          (Analysis.rationalPoleProfile 3 (25 / 51) (7 / 5) (Real.exp (-(y + w))) : ℂ) *
            (Real.exp (-c * |w|) : ℂ) := by
  have h := kernel_resolvent_pole_570 y hc
  have he :
    ((c ^ 2 : ℝ) : ℂ) *
        (∫ t : ℝ,
          (quarterKernel570.function (Complex.I * t) * Complex.exp (Complex.I * (t : ℂ) * y)) *
            ((1 / (c ^ 2 + t ^ 2) : ℝ) : ℂ)) =
      ∫ t : ℝ,
        (quarterKernel570.function (Complex.I * t) * Complex.exp (Complex.I * (t : ℂ) * y)) *
          ((4 : ℂ) / (4 + (((2 / c) * t : ℝ) : ℂ) ^ 2)) := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    apply Filter.Eventually.of_forall
    intro t
    dsimp only
    have hh := congrArg Complex.ofReal (quarter_scaled_resolvent (t := t) hc)
    push_cast at hh ⊢
    rw [hh]
    ring
  rw [mul_assoc, he]
  exact h

/-- Translate the profile convolution to the profile variable. The
exponential kernel is then centered at `y`, the form used to analyze its
individual Gamma poles. -/
theorem kernel_pole_centered_570 (y : ℝ) {c : ℝ} (hc : 0 < c) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * ((c ^ 2 : ℝ) : ℂ) *
        (∫ t : ℝ,
          (quarterKernel570.function (Complex.I * t) * Complex.exp (Complex.I * (t : ℂ) * y)) *
            ((1 / (c ^ 2 + t ^ 2) : ℝ) : ℂ)) =
      ((c / 2 : ℝ) : ℂ) *
        ∫ v : ℝ,
          (Analysis.rationalPoleProfile 3 (25 / 51) (7 / 5) (Real.exp (-v)) : ℂ) *
            (Real.exp (-c * |v - y|) : ℂ) := by
  rw [kernel_pole_convolution_570 y hc]
  apply congrArg (fun z : ℂ ↦ ((c / 2 : ℝ) : ℂ) * z)
  let f : ℝ → ℂ := fun v ↦
    (Analysis.rationalPoleProfile 3 (25 / 51) (7 / 5) (Real.exp (-v)) : ℂ) *
      (Real.exp (-c * |v - y|) : ℂ)
  have h := MeasureTheory.integral_add_left_eq_self (μ := MeasureTheory.volume) f y
  simpa only [f, add_sub_cancel_left] using h

/-- The actual sixth-pole phase is continuous and integrable at every real
logarithmic scale. The exponential phase has unit modulus, so the kernel's
existing line-integrability estimate supplies the bound. -/
theorem gamma_phase_integrable_570 (y : ℝ) :
    Continuous (gammaPhase570 y) ∧
      MeasureTheory.Integrable (gammaPhase570 y) ∧
      MeasureTheory.Integrable
        (fun t : ℝ ↦
          quarterKernel570.function (Complex.I * t) * Complex.exp (Complex.I * (t : ℂ) * y)) := by
  have hp : Continuous (fun t : ℝ ↦ Complex.exp (Complex.I * (t : ℂ) * y)) :=
    Complex.continuous_exp.comp
      ((continuous_const.mul Complex.continuous_ofReal).mul continuous_const)
  have hc := kernel_line_continuous_570.mul hp
  have hk :=
    LLS.PaperStatements.MellinKernel.integrable_line quarterKernel570 (c := 0) (by norm_num only)
      (by linarith only [quarterKernel570.delta_pos])
  have hk' : MeasureTheory.Integrable (fun t : ℝ ↦ quarterKernel570.function (Complex.I * t)) := by
    simpa only [Complex.ofReal_zero, zero_add] using hk
  have hi :
    MeasureTheory.Integrable
      (fun t : ℝ ↦
        quarterKernel570.function (Complex.I * t) * Complex.exp (Complex.I * (t : ℂ) * y)) := by
    apply hk'.mul_bdd (c := 1) hp.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro t
    rw [Complex.norm_exp]
    have hre : (Complex.I * (t : ℂ) * y).re = 0 := by
      simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, mul_zero, sub_zero, one_mul, zero_add]
    rw [hre, Real.exp_zero]
  exact ⟨Complex.continuous_re.comp hc, hi.re, hi⟩

/-- The sixth-pole inverse Mellin profile in its shifted logarithmic
variable. It vanishes for negative arguments and equals the exponential fifth
moment on the positive half-line, including the kernel normalization. -/
noncomputable def gammaDensity570 (v : ℝ) : ℝ :=
  if 0 ≤ v then ((51 / 50 : ℝ) ^ 5 / 120) * v ^ 5 * Real.exp (-(51 / 50 : ℝ) * v) else 0

/-- The inverse Mellin profile at `exp (21/8 - v)` is the shifted density.
The support condition is exactly `0 ≤ v`; on that support the rational pole
formula reduces to an exponential fifth moment. -/
theorem profile_shift_570 (v : ℝ) :
    Analysis.rationalPoleProfile 3 (25 / 51) (7 / 5) (Real.exp (14 / 5 - v)) =
      gammaDensity570 v := by
  unfold Analysis.rationalPoleProfile gammaDensity570
  rw [Real.log_exp]
  by_cases hv : 0 ≤ v
  · rw [ite_eq_left ⟨Real.exp_pos _, by linarith only [hv]⟩, ite_eq_left hv]
    norm_num only [show 2 * 3 - 1 = 5 by decide, Nat.factorial]
    have he : -(((14 / 5 : ℝ) - (14 / 5 - v)) / (50 / 51)) = -(51 / 50 : ℝ) * v := by ring
    rw [he]
    ring
  · rw [ite_eq_right
        (by
          intro h; apply hv; linarith only [h.2]),
      ite_eq_right hv]

/-- The positive-pole resolvent is the convolution of the shifted density
with `exp (-c |v - z|)`, where `z = y + 21/8`. This rewrites the exact
Fourier identity in the logarithmic variables used for the Gamma-tail bound. -/
theorem pole_density_convolution_570 (y : ℝ) {c : ℝ} (hc : 0 < c) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * ((c ^ 2 : ℝ) : ℂ) *
        (∫ t : ℝ,
          (quarterKernel570.function (Complex.I * t) * Complex.exp (Complex.I * (t : ℂ) * y)) *
            ((1 / (c ^ 2 + t ^ 2) : ℝ) : ℂ)) =
      ((c / 2 : ℝ) : ℂ) *
        ∫ v : ℝ, (gammaDensity570 v : ℂ) * (Real.exp (-c * |v - (y + 14 / 5)|) : ℂ) := by
  rw [kernel_pole_centered_570 y hc]
  apply congrArg (fun z : ℂ ↦ ((c / 2 : ℝ) : ℂ) * z)
  let f : ℝ → ℂ := fun v ↦ (gammaDensity570 v : ℂ) * (Real.exp (-c * |v - (y + 14 / 5)|) : ℂ)
  have h := MeasureTheory.integral_add_left_eq_self (μ := MeasureTheory.volume) f (14 / 5 : ℝ)
  calc
    _ = ∫ u : ℝ, f (14 / 5 + u) := by
      apply MeasureTheory.integral_congr_ae
      apply Filter.Eventually.of_forall
      intro u
      dsimp only [f]
      have hu : (14 / 5 : ℝ) - (14 / 5 + u) = -u := by ring
      have harg : (14 / 5 : ℝ) + u - (y + 14 / 5) = u - y := by ring
      rw [← hu, profile_shift_570, harg]
    _ = _ := h

/-- The shifted density vanishes on the nonpositive half-line. Hence the
pole convolution may be restricted to the positive half-line, including at
the boundary where its fifth power is zero. -/
theorem pole_density_positive_570 (y : ℝ) {c : ℝ} (hc : 0 < c) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * ((c ^ 2 : ℝ) : ℂ) *
        (∫ t : ℝ,
          (quarterKernel570.function (Complex.I * t) * Complex.exp (Complex.I * (t : ℂ) * y)) *
            ((1 / (c ^ 2 + t ^ 2) : ℝ) : ℂ)) =
      ((c / 2 : ℝ) : ℂ) *
        ∫ v in Set.Ioi (0 : ℝ),
          (gammaDensity570 v : ℂ) * (Real.exp (-c * |v - (y + 14 / 5)|) : ℂ) := by
  rw [pole_density_convolution_570 y hc]
  apply congrArg (fun z : ℂ ↦ ((c / 2 : ℝ) : ℂ) * z)
  rw [← MeasureTheory.integral_indicator measurableSet_Ioi]
  apply MeasureTheory.integral_congr_ae
  apply Filter.Eventually.of_forall
  intro v
  dsimp only
  by_cases hv : 0 < v
  · rw [Set.indicator_of_mem (show v ∈ Set.Ioi (0 : ℝ) from hv)]
  · rw [Set.indicator_of_notMem (show v ∉ Set.Ioi (0 : ℝ) from hv)]
    have hv0 : v ≤ 0 := le_of_not_gt hv
    have hd : gammaDensity570 v = 0 := by
      by_cases heq : v = 0
      · subst v
        norm_num only [gammaDensity570, le_refl, ite_true, zero_pow, OfNat.ofNat_ne_zero, mul_zero,
          zero_mul]
      · rw [gammaDensity570, ite_eq_right (not_le_of_gt (lt_of_le_of_ne hv0 heq))]
    rw [hd]
    norm_num only [Complex.ofReal_zero, zero_mul]

end PseudoPrime.PrimeTestBounds.MillerRabin
