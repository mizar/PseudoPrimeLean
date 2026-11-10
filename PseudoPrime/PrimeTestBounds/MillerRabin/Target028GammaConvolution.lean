/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028GammaBaseline
public import PseudoPrime.Analysis.ExponentialMeanSquare
public import PseudoPrime.Analysis.ExponentialAbsoluteIntegral
public import PseudoPrime.Analysis.ExponentialFourierProduct

/-! # Positivity of the first even Gamma resolvent -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The product of an integrable continuous frequency weight with the Laplace
Fourier kernel is absolutely integrable. Its norm is bounded by the product of
the frequency norm and the positive exponential weight. -/
theorem target028_laplace_product_integrable (F : ℝ → ℂ) (hF : Continuous F)
    (hi : MeasureTheory.Integrable F) :
    MeasureTheory.Integrable
      (fun p : ℝ × ℝ ↦ F p.1 * Analysis.ExponentialMeanSquare.kernelIntegrand (4 * p.1) p.2)
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
  exact Analysis.exponential_fourier_product_integrable F hF hi 4

/-- The first-pole resolvent integral is a Laplace-weighted average of Fourier
transforms of `F`. Absolute product integrability justifies the exchange, and
the explicit Laplace transform supplies the rational factor. -/
theorem target028_first_pole_integral_eq (F : ℝ → ℂ) (hF : Continuous F)
    (hi : MeasureTheory.Integrable F) :
    (∫ t : ℝ, F t * ((1 / (1 / 4 + t ^ 2) : ℝ) : ℂ)) =
      4 * ∫ v : ℝ, ∫ t : ℝ, F t * Analysis.ExponentialMeanSquare.kernelIntegrand (4 * t) v := by
  have heq (t : ℝ) :
    ((1 / (1 / 4 + t ^ 2) : ℝ) : ℂ) = 4 * ((4 : ℂ) / (4 + ((4 * t : ℝ) : ℂ) ^ 2)) := by
    have hpos : 0 < (1 / 4 : ℝ) + t ^ 2 := by nlinarith only [sq_nonneg t]
    have hne : (4 : ℂ) + ((4 * t : ℝ) : ℂ) ^ 2 ≠ 0 :=
      Analysis.ExponentialMeanSquare.kernel_denominator_ne_zero (4 * t)
    push_cast
    field_simp
  calc
    _ = 4 * ∫ t : ℝ, F t * ((4 : ℂ) / (4 + ((4 * t : ℝ) : ℂ) ^ 2)) := by
      rw [← MeasureTheory.integral_const_mul]
      apply MeasureTheory.integral_congr_ae
      apply Filter.Eventually.of_forall
      intro t
      dsimp only
      rw [heq]
      ring
    _ = _ := by rw [Analysis.exponential_fourier_resolvent_eq F hF hi 4]

/-- If every Fourier transform of an integrable continuous frequency weight
has nonnegative real part, then its first-pole resolvent integral also has
nonnegative real part. The Laplace density is everywhere positive. -/
theorem target028_first_pole_integral_nonneg (F : ℝ → ℂ) (hF : Continuous F)
    (hi : MeasureTheory.Integrable F)
    (hpos : ∀ v : ℝ, 0 ≤ (∫ t : ℝ, F t * Complex.exp (Complex.I * (4 * (t : ℂ)) * v)).re) :
    0 ≤ (∫ t : ℝ, F t * ((1 / (1 / 4 + t ^ 2) : ℝ) : ℂ)).re := by
  rw [target028_first_pole_integral_eq F hF hi]
  rw [← Analysis.exponential_fourier_resolvent_eq F hF hi 4]
  change 0 ≤ (((4 : ℝ) : ℂ) * _).re
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_nonneg (by norm_num only) (Analysis.exponential_fourier_resolvent_nonneg F hF hi 4 hpos)

/-- The Fourier transform of the sixth-pole kernel is its inverse Mellin
profile at `exp (-y)`, with the exact Fourier normalization. This identity
also supplies the profile inside the scaled resolvent convolution. -/
theorem quarter_kernel_fourier_eq (y : ℝ) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          refinedSixPoleKernel.function (Complex.I * t) * Complex.exp (Complex.I * (t : ℂ) * y)) =
      (Analysis.rationalPoleProfile 3 (25 / 54) (21 / 16) (Real.exp (-y)) : ℂ) := by
  have hu : 0 < Real.exp (-y) := Real.exp_pos _
  have hinv := refined_six_pole_inversion (σ := 0) (u := Real.exp (-y)) (by norm_num only) hu
  have hphase (t : ℝ) :
    (Real.exp (-y) : ℂ) ^ (-(Complex.I * t)) = Complex.exp (Complex.I * (t : ℂ) * y) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hu.ne'), ← Complex.ofReal_log hu.le]
    rw [Real.log_exp, Complex.ofReal_neg]
    congr 1
    ring
  unfold Analysis.inverseMellin at hinv
  simpa only [Complex.ofReal_zero, zero_add, hphase] using hinv

/-- The Fourier integral of the sixth-pole kernel is its nonnegative inverse
Mellin profile at an exponential argument. This expresses the sign needed for
the first Gamma pole without taking the absolute value of the oscillatory kernel. -/
theorem target028_kernel_fourier_nonneg (y : ℝ) :
    0 ≤
      (∫ t : ℝ,
          refinedSixPoleKernel.function (Complex.I * t) *
            Complex.exp (Complex.I * (t : ℂ) * y)).re := by
  have hr := congrArg Complex.re (quarter_kernel_fourier_eq y)
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hr
  have hp := refined_six_pole_profile_nonneg (Real.exp (-y))
  have hc : 0 < (1 / (2 * Real.pi) : ℝ) :=
    div_pos zero_lt_one (mul_pos (by norm_num only) Real.pi_pos)
  exact nonneg_of_mul_nonneg_left (by linarith only [hr, hp]) hc

/-- The sixth-pole kernel is continuous on the imaginary axis, which stays
strictly to the right of its unique pole. This permits the product Fubini
estimate to be applied to the actual Gamma kernel. -/
theorem target028_kernel_line_continuous :
    Continuous (fun t : ℝ ↦ refinedSixPoleKernel.function (Complex.I * t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hden : Complex.I * (t : ℂ) + 27 / 25 ≠ 0 := by
    intro h
    have h27 : (27 / 25 : ℂ) = (((27 / 25 : ℝ)) : ℂ) := by
      push_cast
      ring
    rw [h27] at h
    have hr := congrArg Complex.re h
    norm_num only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, Complex.zero_re] at hr
  have he :
    (fun t : ℝ ↦ refinedSixPoleKernel.function (Complex.I * t)) = fun t : ℝ ↦
      ((27 / 25 : ℂ) ^ 5) *
        (Complex.exp ((21 / 8 : ℂ) * (Complex.I * t)) / (Complex.I * t + 27 / 25) ^ 6) := by
    funext t
    exact refined_six_pole_function (Complex.I * t)
  rw [he]
  fun_prop (disch := exact pow_ne_zero 6 hden)

/-- The sixth-pole kernel multiplied by a real Fourier phase remains
continuous and integrable. The phase has unit norm, so the Mellin-kernel
integrability estimate applies at every shift. -/
theorem quarter_kernel_phase_regular (y : ℝ) :
    Continuous
        (fun t : ℝ ↦
          refinedSixPoleKernel.function (Complex.I * t) * Complex.exp (Complex.I * (t : ℂ) * y)) ∧
      MeasureTheory.Integrable
        (fun t : ℝ ↦
          refinedSixPoleKernel.function (Complex.I * t) *
            Complex.exp (Complex.I * (t : ℂ) * y)) := by
  have hp : Continuous (fun t : ℝ ↦ Complex.exp (Complex.I * (t : ℂ) * y)) :=
    Complex.continuous_exp.comp
      ((continuous_const.mul Complex.continuous_ofReal).mul continuous_const)
  constructor
  · exact target028_kernel_line_continuous.mul hp
  · have hk :=
      LLS.PaperStatements.MellinKernel.integrable_line refinedSixPoleKernel (c := 0)
        (by norm_num only) (by linarith only [refinedSixPoleKernel.delta_pos])
    have hk' :
      MeasureTheory.Integrable (fun t : ℝ ↦ refinedSixPoleKernel.function (Complex.I * t)) := by
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
theorem quarter_kernel_resolvent_convolution (y s : ℝ) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          (refinedSixPoleKernel.function (Complex.I * t) * Complex.exp (Complex.I * (t : ℂ) * y)) *
            ((4 : ℂ) / (4 + ((s * t : ℝ) : ℂ) ^ 2))) =
      ∫ v : ℝ,
        (Analysis.rationalPoleProfile 3 (25 / 54) (21 / 16) (Real.exp (-(y + s * v))) : ℂ) *
          (Analysis.ExponentialMeanSquare.weight v : ℂ) := by
  let F : ℝ → ℂ := fun t ↦
    refinedSixPoleKernel.function (Complex.I * t) * Complex.exp (Complex.I * (t : ℂ) * y)
  have hf : Continuous F := (quarter_kernel_phase_regular y).1
  have hi : MeasureTheory.Integrable F := (quarter_kernel_phase_regular y).2
  rw [Analysis.exponential_fourier_resolvent_convolution F hf hi s, ←
    MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_congr_ae
  apply Filter.Eventually.of_forall
  intro v
  dsimp only
  have he :
    (∫ t : ℝ, F t * Complex.exp (Complex.I * (s * (t : ℂ)) * v)) =
      ∫ t : ℝ,
        refinedSixPoleKernel.function (Complex.I * t) *
          Complex.exp (Complex.I * (t : ℂ) * (y + s * v : ℝ)) := by
    apply MeasureTheory.integral_congr_ae
    apply Filter.Eventually.of_forall
    intro t
    dsimp only [F]
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [← mul_assoc, he, quarter_kernel_fourier_eq]

/-- For a positive pole parameter, rescale the sixth-pole convolution so
that its exponential kernel has decay rate `c`. The prefactor is the exact
Jacobian `c / 2`. -/
theorem quarter_kernel_resolvent_pole (y : ℝ) {c : ℝ} (hc : 0 < c) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          (refinedSixPoleKernel.function (Complex.I * t) * Complex.exp (Complex.I * (t : ℂ) * y)) *
            ((4 : ℂ) / (4 + (((2 / c) * t : ℝ) : ℂ) ^ 2))) =
      ((c / 2 : ℝ) : ℂ) *
        ∫ w : ℝ,
          (Analysis.rationalPoleProfile 3 (25 / 54) (21 / 16) (Real.exp (-(y + w))) : ℂ) *
            (Real.exp (-c * |w|) : ℂ) := by
  rw [quarter_kernel_resolvent_convolution y (2 / c)]
  let g : ℝ → ℂ := fun w ↦
    (Analysis.rationalPoleProfile 3 (25 / 54) (21 / 16) (Real.exp (-(y + w))) : ℂ)
  have hs : 0 < 2 / c := div_pos (by norm_num only) hc
  have h := Analysis.exponential_convolution_rescale g hs
  have he : 2 / (2 / c) = c := by
    rw [div_div_eq_mul_div, mul_div_cancel_left₀ c (by norm_num only : (2 : ℝ) ≠ 0)]
  have hi : (2 / c)⁻¹ = c / 2 := by rw [inv_div]
  simpa only [g, he, ← Complex.ofReal_inv, hi] using h

/-- The scaled exponential resolvent equals the usual resolvent normalized
by `c²`. Positivity of `c` makes both denominators nonzero. -/
theorem quarter_scaled_resolvent {c t : ℝ} (hc : 0 < c) :
    4 / (4 + ((2 / c) * t) ^ 2) = c ^ 2 / (c ^ 2 + t ^ 2) := by
  have hd1 : (4 : ℝ) + (2 / c * t) ^ 2 ≠ 0 := by positivity
  have hd2 : c ^ 2 + t ^ 2 ≠ 0 := by positivity
  have htc : (2 / c * t) * c = 2 * t := by
    rw [mul_assoc, mul_comm t c, ← mul_assoc, div_mul_cancel₀ _ hc.ne']
  have hp : (2 / c * t) ^ 2 * c ^ 2 = (2 * t) ^ 2 := by rw [← mul_pow, htc]
  apply (div_eq_div_iff hd1 hd2).2
  nlinarith only [hp]

/-- The usual resolvent at a positive pole has the same profile convolution
after multiplying its Fourier integral by `c²`. This exact form keeps the
normalization explicit for the even-Gamma partial fractions. -/
theorem quarter_kernel_pole_convolution (y : ℝ) {c : ℝ} (hc : 0 < c) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * ((c ^ 2 : ℝ) : ℂ) *
        (∫ t : ℝ,
          (refinedSixPoleKernel.function (Complex.I * t) * Complex.exp (Complex.I * (t : ℂ) * y)) *
            ((1 / (c ^ 2 + t ^ 2) : ℝ) : ℂ)) =
      ((c / 2 : ℝ) : ℂ) *
        ∫ w : ℝ,
          (Analysis.rationalPoleProfile 3 (25 / 54) (21 / 16) (Real.exp (-(y + w))) : ℂ) *
            (Real.exp (-c * |w|) : ℂ) := by
  have h := quarter_kernel_resolvent_pole y hc
  have he :
    ((c ^ 2 : ℝ) : ℂ) *
        (∫ t : ℝ,
          (refinedSixPoleKernel.function (Complex.I * t) * Complex.exp (Complex.I * (t : ℂ) * y)) *
            ((1 / (c ^ 2 + t ^ 2) : ℝ) : ℂ)) =
      ∫ t : ℝ,
        (refinedSixPoleKernel.function (Complex.I * t) * Complex.exp (Complex.I * (t : ℂ) * y)) *
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
theorem quarter_kernel_pole_centered (y : ℝ) {c : ℝ} (hc : 0 < c) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * ((c ^ 2 : ℝ) : ℂ) *
        (∫ t : ℝ,
          (refinedSixPoleKernel.function (Complex.I * t) * Complex.exp (Complex.I * (t : ℂ) * y)) *
            ((1 / (c ^ 2 + t ^ 2) : ℝ) : ℂ)) =
      ((c / 2 : ℝ) : ℂ) *
        ∫ v : ℝ,
          (Analysis.rationalPoleProfile 3 (25 / 54) (21 / 16) (Real.exp (-v)) : ℂ) *
            (Real.exp (-c * |v - y|) : ℂ) := by
  rw [quarter_kernel_pole_convolution y hc]
  congr 1
  let f : ℝ → ℂ := fun v ↦
    (Analysis.rationalPoleProfile 3 (25 / 54) (21 / 16) (Real.exp (-v)) : ℂ) *
      (Real.exp (-c * |v - y|) : ℂ)
  have h := MeasureTheory.integral_add_left_eq_self (μ := MeasureTheory.volume) f y
  simpa only [f, add_sub_cancel_left] using h

/-- For every logarithmic scale, the first even-Gamma pole contributes a
nonnegative resolvent integral. The positive Laplace convolution of the
nonnegative inverse-Mellin profile proves the sign for the actual kernel. -/
theorem target028_first_pole_kernel_nonneg (y : ℝ) :
    0 ≤
      (∫ t : ℝ,
          (refinedSixPoleKernel.function (Complex.I * t) * Complex.exp (Complex.I * (t : ℂ) * y)) *
            ((1 / (1 / 4 + t ^ 2) : ℝ) : ℂ)).re := by
  let F : ℝ → ℂ := fun t ↦
    refinedSixPoleKernel.function (Complex.I * t) * Complex.exp (Complex.I * (t : ℂ) * y)
  have hf : Continuous F := (quarter_kernel_phase_regular y).1
  have hi : MeasureTheory.Integrable F := (quarter_kernel_phase_regular y).2
  apply target028_first_pole_integral_nonneg F hf hi
  intro v
  have h := target028_kernel_fourier_nonneg (y + 4 * v)
  apply h.trans_eq
  congr 2
  funext t
  dsimp only [F]
  conv_rhs => rw [mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- Every real resolvent scale has nonnegative contribution for the shifted
sixth-pole kernel. The inverse Mellin profile supplies the nonnegative Fourier
transforms, and the general exponential convolution transfers their sign. -/
theorem quarter_scaled_pole_kernel_nonneg (y s : ℝ) :
    0 ≤
      (∫ t : ℝ,
          (refinedSixPoleKernel.function (Complex.I * t) * Complex.exp (Complex.I * (t : ℂ) * y)) *
            ((4 : ℂ) / (4 + ((s * t : ℝ) : ℂ) ^ 2))).re := by
  let F : ℝ → ℂ := fun t ↦
    refinedSixPoleKernel.function (Complex.I * t) * Complex.exp (Complex.I * (t : ℂ) * y)
  have hf : Continuous F := (quarter_kernel_phase_regular y).1
  have hi : MeasureTheory.Integrable F := (quarter_kernel_phase_regular y).2
  apply Analysis.exponential_fourier_resolvent_nonneg F hf hi s
  intro v
  have h := target028_kernel_fourier_nonneg (y + s * v)
  apply h.trans_eq
  congr 2
  funext t
  dsimp only [F]
  conv_rhs => rw [mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

end PseudoPrime.PrimeTestBounds.MillerRabin
