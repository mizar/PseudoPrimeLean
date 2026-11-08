/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028GammaBaseline
public import PseudoPrime.Analysis.ExponentialMeanSquare
public import PseudoPrime.Analysis.ExponentialAbsoluteIntegral

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
  have hw : MeasureTheory.Integrable Analysis.ExponentialMeanSquare.weight := by
    exact Analysis.integrable_exp_neg_mul_abs (by norm_num only : (0 : ℝ) < 2)
  have hm := hi.norm.mul_prod hw
  have hf : Continuous (fun p : ℝ × ℝ ↦ F p.1) := hF.comp continuous_fst
  have hwc : Continuous (fun p : ℝ × ℝ ↦ (Analysis.ExponentialMeanSquare.weight p.2 : ℂ)) := by
    apply Complex.continuous_ofReal.comp
    exact Real.continuous_exp.comp (continuous_const.mul (continuous_abs.comp continuous_snd))
  have he : Continuous (fun p : ℝ × ℝ ↦ Complex.exp (Complex.I * (4 * (p.1 : ℂ)) * p.2)) := by
    apply Complex.continuous_exp.comp
    exact
      (continuous_const.mul
            (continuous_const.mul (Complex.continuous_ofReal.comp continuous_fst))).mul
        (Complex.continuous_ofReal.comp continuous_snd)
  have hmeas :
    MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ ↦ F p.1 * Analysis.ExponentialMeanSquare.kernelIntegrand (4 * p.1) p.2)
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
    have hc :=
      (hf.mul (he.mul hwc)).aestronglyMeasurable (μ :=
        MeasureTheory.volume.prod MeasureTheory.volume)
    convert hc using 1
    funext p
    simp only [Analysis.ExponentialMeanSquare.kernelIntegrand, Pi.mul_apply, Complex.ofReal_mul,
      Complex.ofReal_ofNat]
  apply hm.mono' hmeas
  apply MeasureTheory.ae_of_all
  intro p
  dsimp only [Analysis.ExponentialMeanSquare.kernelIntegrand, Pi.mul_apply, Function.comp_apply]
  have hwpos : 0 ≤ Analysis.ExponentialMeanSquare.weight p.2 := (Real.exp_pos _).le
  rw [norm_mul, norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hwpos]
  have hre : (Complex.I * (↑(4 * p.1) : ℂ) * (p.2 : ℂ)).re = 0 := by
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, one_mul, zero_add]
  rw [hre, Real.exp_zero, one_mul]

/-- The first-pole resolvent integral is a Laplace-weighted average of Fourier
transforms of `F`. Absolute product integrability justifies the exchange, and
the explicit Laplace transform supplies the rational factor. -/
theorem target028_first_pole_integral_eq (F : ℝ → ℂ) (hF : Continuous F)
    (hi : MeasureTheory.Integrable F) :
    (∫ t : ℝ, F t * ((1 / (1 / 4 + t ^ 2) : ℝ) : ℂ)) =
      4 * ∫ v : ℝ, ∫ t : ℝ, F t * Analysis.ExponentialMeanSquare.kernelIntegrand (4 * t) v := by
  have hprod := target028_laplace_product_integrable F hF hi
  have heq (t : ℝ) :
    ((1 / (1 / 4 + t ^ 2) : ℝ) : ℂ) = 4 * ((4 : ℂ) / (4 + ((4 * t : ℝ) : ℂ) ^ 2)) := by
    have hpos : 0 < (1 / 4 : ℝ) + t ^ 2 := by nlinarith only [sq_nonneg t]
    have hne : (4 : ℂ) + ((4 * t : ℝ) : ℂ) ^ 2 ≠ 0 :=
      Analysis.ExponentialMeanSquare.kernel_denominator_ne_zero (4 * t)
    push_cast
    field_simp
  calc
    _ = 4 * ∫ t : ℝ, ∫ v : ℝ, F t * Analysis.ExponentialMeanSquare.kernelIntegrand (4 * t) v := by
      rw [← MeasureTheory.integral_const_mul]
      apply MeasureTheory.integral_congr_ae
      apply Filter.Eventually.of_forall
      intro t
      dsimp only
      rw [MeasureTheory.integral_const_mul, Analysis.ExponentialMeanSquare.integral_kernelIntegrand,
        heq]
      ring
    _ = _ := by rw [MeasureTheory.integral_integral_swap hprod]

/-- If every Fourier transform of an integrable continuous frequency weight
has nonnegative real part, then its first-pole resolvent integral also has
nonnegative real part. The Laplace density is everywhere positive. -/
theorem target028_first_pole_integral_nonneg (F : ℝ → ℂ) (hF : Continuous F)
    (hi : MeasureTheory.Integrable F)
    (hpos : ∀ v : ℝ, 0 ≤ (∫ t : ℝ, F t * Complex.exp (Complex.I * (4 * (t : ℂ)) * v)).re) :
    0 ≤ (∫ t : ℝ, F t * ((1 / (1 / 4 + t ^ 2) : ℝ) : ℂ)).re := by
  rw [target028_first_pole_integral_eq F hF hi]
  change 0 ≤ (((4 : ℝ) : ℂ) * _).re
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  apply mul_nonneg (by norm_num only)
  have hprod := target028_laplace_product_integrable F hF hi
  have hout := hprod.integral_prod_right
  have hre := Complex.reCLM.integral_comp_comm hout
  change
    (∫ v : ℝ, (∫ t : ℝ, F t * Analysis.ExponentialMeanSquare.kernelIntegrand (4 * t) v).re) =
      (∫ v : ℝ, ∫ t : ℝ, F t * Analysis.ExponentialMeanSquare.kernelIntegrand (4 * t) v).re at hre
  rw [← hre]
  apply MeasureTheory.integral_nonneg
  intro v
  have he :
    (∫ t : ℝ, F t * Analysis.ExponentialMeanSquare.kernelIntegrand (4 * t) v) =
      (∫ t : ℝ, F t * Complex.exp (Complex.I * (4 * (t : ℂ)) * v)) *
        (Analysis.ExponentialMeanSquare.weight v : ℂ) := by
    rw [← MeasureTheory.integral_mul_const]
    apply MeasureTheory.integral_congr_ae
    apply Filter.Eventually.of_forall
    intro t
    simp only [Analysis.ExponentialMeanSquare.kernelIntegrand, Complex.ofReal_mul,
      Complex.ofReal_ofNat]
    ring
  change 0 ≤ (∫ t : ℝ, F t * Analysis.ExponentialMeanSquare.kernelIntegrand (4 * t) v).re
  rw [he, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  exact mul_nonneg (hpos v) (Real.exp_pos _).le

/-- The Fourier integral of the sixth-pole kernel is its nonnegative inverse
Mellin profile at an exponential argument. This expresses the sign needed for
the first Gamma pole without taking the absolute value of the oscillatory kernel. -/
theorem target028_kernel_fourier_nonneg (y : ℝ) :
    0 ≤
      (∫ t : ℝ,
          refinedSixPoleKernel.function (Complex.I * t) *
            Complex.exp (Complex.I * (t : ℂ) * y)).re := by
  let u : ℝ := Real.exp (-y)
  have hu : 0 < u := Real.exp_pos _
  have hinv := refined_six_pole_inversion (σ := 0) (u := u) (by norm_num only) hu
  have hphase (t : ℝ) : (u : ℂ) ^ (-(Complex.I * t)) = Complex.exp (Complex.I * (t : ℂ) * y) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hu.ne'), ← Complex.ofReal_log hu.le]
    have hl : Real.log u = -y := by simp only [u, Real.log_exp]
    rw [hl, Complex.ofReal_neg]
    congr 1
    ring
  unfold Analysis.inverseMellin at hinv
  simp only [Complex.ofReal_zero, zero_add, hphase] at hinv
  have hr := congrArg Complex.re hinv
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hr
  have hp := refined_six_pole_profile_nonneg u
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
  have hp : Continuous (fun t : ℝ ↦ Complex.exp (Complex.I * (t : ℂ) * y)) :=
    Complex.continuous_exp.comp
      ((continuous_const.mul Complex.continuous_ofReal).mul continuous_const)
  have hf : Continuous F := target028_kernel_line_continuous.mul hp
  have hk :=
    LLS.PaperStatements.MellinKernel.integrable_line refinedSixPoleKernel (c := 0)
      (by norm_num only) (by linarith only [refinedSixPoleKernel.delta_pos])
  have hk' :
    MeasureTheory.Integrable (fun t : ℝ ↦ refinedSixPoleKernel.function (Complex.I * t)) := by
    simpa only [Complex.ofReal_zero, zero_add] using hk
  have hi : MeasureTheory.Integrable F := by
    apply hk'.mul_bdd (c := 1) hp.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro t
    rw [Complex.norm_exp]
    have hre : (Complex.I * (t : ℂ) * y).re = 0 := by
      simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, mul_zero, sub_zero, one_mul, zero_add]
    rw [hre, Real.exp_zero]
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

end PseudoPrime.PrimeTestBounds.MillerRabin
