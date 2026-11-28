/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMainGamma644
import all PseudoPrime.PrimeTestBounds.MillerRabin.Target028GammaConvolution

/-! # Gamma resolvent convolution for the section 122 main kernel -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The Fourier transform of the sixth-pole kernel is its inverse Mellin
profile at `exp (-y)`, with the exact Fourier normalization. This identity
also supplies the profile inside the scaled resolvent convolution. -/
theorem quarter_main_fourier_644 (y : ℝ) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          quarterKernel644.function (Complex.I * t) * Complex.exp (Complex.I * (t : ℂ) * y)) =
      (Analysis.rationalPoleProfile 3 (50 / 107) (2687 / 2000) (Real.exp (-y)) : ℂ) := by
  have hu : 0 < Real.exp (-y) := Real.exp_pos _
  have hinv := quarter_main_inversion_644 (σ := 0) (u := Real.exp (-y)) (by norm_num only) hu
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
theorem quarter_main_line_cont_644 :
    Continuous (fun t : ℝ ↦ quarterKernel644.function (Complex.I * t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hden : Complex.I * (t : ℂ) + 107 / 100 ≠ 0 := by
    intro h
    have h27 : (107 / 100 : ℂ) = (((107 / 100 : ℝ)) : ℂ) := by
      push_cast
      ring
    rw [h27] at h
    have hr := congrArg Complex.re h
    norm_num only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, Complex.zero_re] at hr
  have he :
    (fun t : ℝ ↦ quarterKernel644.function (Complex.I * t)) = fun t : ℝ ↦
      ((107 / 100 : ℂ) ^ 5) *
        (Complex.exp ((2687 / 1000 : ℂ) * (Complex.I * t)) / (Complex.I * t + 107 / 100) ^ 6) := by
    funext t
    simpa only [mul_div_assoc] using quarter_function_644 (Complex.I * t)
  rw [he]
  fun_prop (disch := exact pow_ne_zero 6 hden)

/-- The sixth-pole kernel multiplied by a real Fourier phase remains
continuous and integrable. The phase has unit norm, so the Mellin-kernel
integrability estimate applies at every shift. -/
theorem quarter_main_phase_regular_644 (y : ℝ) :
    Continuous
        (fun t : ℝ ↦
          quarterKernel644.function (Complex.I * t) * Complex.exp (Complex.I * (t : ℂ) * y)) ∧
      MeasureTheory.Integrable
        (fun t : ℝ ↦
          quarterKernel644.function (Complex.I * t) * Complex.exp (Complex.I * (t : ℂ) * y)) := by
  have hp : Continuous (fun t : ℝ ↦ Complex.exp (Complex.I * (t : ℂ) * y)) :=
    Complex.continuous_exp.comp
      ((continuous_const.mul Complex.continuous_ofReal).mul continuous_const)
  constructor
  · exact quarter_main_line_cont_644.mul hp
  · have hk :=
      LLS.PaperStatements.MellinKernel.integrable_line quarterKernel644 (c := 0) (by norm_num only)
        (by linarith only [quarterKernel644.delta_pos])
    have hk' :
      MeasureTheory.Integrable (fun t : ℝ ↦ quarterKernel644.function (Complex.I * t)) := by
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
theorem quarter_main_resolvent_644 (y s : ℝ) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          (quarterKernel644.function (Complex.I * t) * Complex.exp (Complex.I * (t : ℂ) * y)) *
            ((4 : ℂ) / (4 + ((s * t : ℝ) : ℂ) ^ 2))) =
      ∫ v : ℝ,
        (Analysis.rationalPoleProfile 3 (50 / 107) (2687 / 2000) (Real.exp (-(y + s * v))) : ℂ) *
          (Analysis.ExponentialMeanSquare.weight v : ℂ) := by
  let F : ℝ → ℂ := fun t ↦
    quarterKernel644.function (Complex.I * t) * Complex.exp (Complex.I * (t : ℂ) * y)
  have hf : Continuous F := (quarter_main_phase_regular_644 y).1
  have hi : MeasureTheory.Integrable F := (quarter_main_phase_regular_644 y).2
  rw [Analysis.exponential_fourier_resolvent_convolution F hf hi s, ←
    MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_congr_ae
  apply Filter.Eventually.of_forall
  intro v
  dsimp only
  have he :
    (∫ t : ℝ, F t * Complex.exp (Complex.I * (s * (t : ℂ)) * v)) =
      ∫ t : ℝ,
        quarterKernel644.function (Complex.I * t) *
          Complex.exp (Complex.I * (t : ℂ) * (y + s * v : ℝ)) := by
    apply MeasureTheory.integral_congr_ae
    apply Filter.Eventually.of_forall
    intro t
    dsimp only [F]
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [← mul_assoc, he, quarter_main_fourier_644]

/-- For a positive pole parameter, rescale the sixth-pole convolution so
that its exponential kernel has decay rate `c`. The prefactor is the exact
Jacobian `c / 2`. -/
theorem quarter_main_resolvent_pole_644 (y : ℝ) {c : ℝ} (hc : 0 < c) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          (quarterKernel644.function (Complex.I * t) * Complex.exp (Complex.I * (t : ℂ) * y)) *
            ((4 : ℂ) / (4 + (((2 / c) * t : ℝ) : ℂ) ^ 2))) =
      ((c / 2 : ℝ) : ℂ) *
        ∫ w : ℝ,
          (Analysis.rationalPoleProfile 3 (50 / 107) (2687 / 2000) (Real.exp (-(y + w))) : ℂ) *
            (Real.exp (-c * |w|) : ℂ) := by
  rw [quarter_main_resolvent_644 y (2 / c)]
  let g : ℝ → ℂ := fun w ↦
    (Analysis.rationalPoleProfile 3 (50 / 107) (2687 / 2000) (Real.exp (-(y + w))) : ℂ)
  have hs : 0 < 2 / c := div_pos (by norm_num only) hc
  have h := Analysis.exponential_convolution_rescale g hs
  have he : 2 / (2 / c) = c := by
    rw [div_div_eq_mul_div, mul_div_cancel_left₀ c (by norm_num only : (2 : ℝ) ≠ 0)]
  have hi : (2 / c)⁻¹ = c / 2 := by rw [inv_div]
  simpa only [g, he, ← Complex.ofReal_inv, hi] using h

/-- The usual resolvent at a positive pole has the same profile convolution
after multiplying its Fourier integral by `c²`. This exact form keeps the
normalization explicit for the even-Gamma partial fractions. -/
theorem quarter_main_pole_conv_644 (y : ℝ) {c : ℝ} (hc : 0 < c) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * ((c ^ 2 : ℝ) : ℂ) *
        (∫ t : ℝ,
          (quarterKernel644.function (Complex.I * t) * Complex.exp (Complex.I * (t : ℂ) * y)) *
            ((1 / (c ^ 2 + t ^ 2) : ℝ) : ℂ)) =
      ((c / 2 : ℝ) : ℂ) *
        ∫ w : ℝ,
          (Analysis.rationalPoleProfile 3 (50 / 107) (2687 / 2000) (Real.exp (-(y + w))) : ℂ) *
            (Real.exp (-c * |w|) : ℂ) := by
  have h := quarter_main_resolvent_pole_644 y hc
  have he :
    ((c ^ 2 : ℝ) : ℂ) *
        (∫ t : ℝ,
          (quarterKernel644.function (Complex.I * t) * Complex.exp (Complex.I * (t : ℂ) * y)) *
            ((1 / (c ^ 2 + t ^ 2) : ℝ) : ℂ)) =
      ∫ t : ℝ,
        (quarterKernel644.function (Complex.I * t) * Complex.exp (Complex.I * (t : ℂ) * y)) *
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
theorem quarter_main_pole_centered_644 (y : ℝ) {c : ℝ} (hc : 0 < c) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * ((c ^ 2 : ℝ) : ℂ) *
        (∫ t : ℝ,
          (quarterKernel644.function (Complex.I * t) * Complex.exp (Complex.I * (t : ℂ) * y)) *
            ((1 / (c ^ 2 + t ^ 2) : ℝ) : ℂ)) =
      ((c / 2 : ℝ) : ℂ) *
        ∫ v : ℝ,
          (Analysis.rationalPoleProfile 3 (50 / 107) (2687 / 2000) (Real.exp (-v)) : ℂ) *
            (Real.exp (-c * |v - y|) : ℂ) := by
  rw [quarter_main_pole_conv_644 y hc]
  congr 1
  let f : ℝ → ℂ := fun v ↦
    (Analysis.rationalPoleProfile 3 (50 / 107) (2687 / 2000) (Real.exp (-v)) : ℂ) *
      (Real.exp (-c * |v - y|) : ℂ)
  have h := MeasureTheory.integral_add_left_eq_self (μ := MeasureTheory.volume) f y
  simpa only [f, add_sub_cancel_left] using h

/-- The sixth-pole inverse Mellin profile in its shifted logarithmic
variable. It vanishes for negative arguments and equals the exponential fifth
moment on the positive half-line, including the kernel normalization. -/
noncomputable def quarterGammaDensity644 (v : ℝ) : ℝ :=
  if 0 ≤ v then ((107 / 100 : ℝ) ^ 5 / 120) * v ^ 5 * Real.exp (-(107 / 100 : ℝ) * v) else 0

/-- The inverse Mellin profile at `exp (21/8 - v)` is the shifted density.
The support condition is exactly `0 ≤ v`; on that support the rational pole
formula reduces to an exponential fifth moment. -/
theorem quarter_profile_shift_644 (v : ℝ) :
    Analysis.rationalPoleProfile 3 (50 / 107) (2687 / 2000) (Real.exp (2687 / 1000 - v)) =
      quarterGammaDensity644 v := by
  unfold Analysis.rationalPoleProfile quarterGammaDensity644
  rw [Real.log_exp]
  by_cases hv : 0 ≤ v
  · rw [ite_eq_left ⟨Real.exp_pos _, by linarith only [hv]⟩, ite_eq_left hv]
    norm_num only [show 2 * 3 - 1 = 5 by decide, Nat.factorial]
    have he : -(((2687 / 1000 : ℝ) - (2687 / 1000 - v)) / (100 / 107)) = -(107 / 100 : ℝ) * v := by
      ring
    rw [he]
    ring
  · rw [ite_eq_right
        (by
          intro h; apply hv; linarith only [h.2]),
      ite_eq_right hv]

/-- The positive-pole resolvent is the convolution of the shifted density
with `exp (-c |v - z|)`, where `z = y + 2687/1000`. This rewrites the exact
Fourier identity in the logarithmic variables used for the Gamma-tail bound. -/
theorem quarter_pole_density_conv_644 (y : ℝ) {c : ℝ} (hc : 0 < c) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * ((c ^ 2 : ℝ) : ℂ) *
        (∫ t : ℝ,
          (quarterKernel644.function (Complex.I * t) * Complex.exp (Complex.I * (t : ℂ) * y)) *
            ((1 / (c ^ 2 + t ^ 2) : ℝ) : ℂ)) =
      ((c / 2 : ℝ) : ℂ) *
        ∫ v : ℝ,
          (quarterGammaDensity644 v : ℂ) * (Real.exp (-c * |v - (y + 2687 / 1000)|) : ℂ) := by
  rw [quarter_main_pole_centered_644 y hc]
  congr 1
  let f : ℝ → ℂ := fun v ↦
    (quarterGammaDensity644 v : ℂ) * (Real.exp (-c * |v - (y + 2687 / 1000)|) : ℂ)
  have h := MeasureTheory.integral_add_left_eq_self (μ := MeasureTheory.volume) f (2687 / 1000 : ℝ)
  calc
    _ = ∫ u : ℝ, f (2687 / 1000 + u) := by
      apply MeasureTheory.integral_congr_ae
      apply Filter.Eventually.of_forall
      intro u
      dsimp only [f]
      have hu : (2687 / 1000 : ℝ) - (2687 / 1000 + u) = -u := by ring
      have harg : (2687 / 1000 : ℝ) + u - (y + 2687 / 1000) = u - y := by ring
      rw [← hu, quarter_profile_shift_644, harg]
    _ = _ := h

/-- The shifted density vanishes on the nonpositive half-line. Hence the
pole convolution may be restricted to the positive half-line, including at
the boundary where its fifth power is zero. -/
theorem quarter_pole_density_pos_644 (y : ℝ) {c : ℝ} (hc : 0 < c) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * ((c ^ 2 : ℝ) : ℂ) *
        (∫ t : ℝ,
          (quarterKernel644.function (Complex.I * t) * Complex.exp (Complex.I * (t : ℂ) * y)) *
            ((1 / (c ^ 2 + t ^ 2) : ℝ) : ℂ)) =
      ((c / 2 : ℝ) : ℂ) *
        ∫ v in Set.Ioi (0 : ℝ),
          (quarterGammaDensity644 v : ℂ) * (Real.exp (-c * |v - (y + 2687 / 1000)|) : ℂ) := by
  rw [quarter_pole_density_conv_644 y hc]
  congr 1
  rw [← MeasureTheory.integral_indicator measurableSet_Ioi]
  apply MeasureTheory.integral_congr_ae
  apply Filter.Eventually.of_forall
  intro v
  dsimp only
  by_cases hv : 0 < v
  · rw [Set.indicator_of_mem (show v ∈ Set.Ioi (0 : ℝ) from hv)]
  · rw [Set.indicator_of_notMem (show v ∉ Set.Ioi (0 : ℝ) from hv)]
    have hv0 : v ≤ 0 := le_of_not_gt hv
    have hd : quarterGammaDensity644 v = 0 := by
      by_cases heq : v = 0
      · subst v
        norm_num only [quarterGammaDensity644, le_refl, ite_true, zero_pow, OfNat.ofNat_ne_zero,
          mul_zero, zero_mul]
      · rw [quarterGammaDensity644, ite_eq_right (not_le_of_gt (lt_of_le_of_ne hv0 heq))]
    rw [hd]
    norm_num only [Complex.ofReal_zero, zero_mul]

/-- The shifted profile convolved with an exponential of rate `c`, over
the profile's positive support. This is the individual pole contribution
used in the even-Gamma tail estimate. -/
noncomputable def quarterGammaConvolution644 (z c : ℝ) : ℝ :=
  ∫ v in Set.Ioi (0 : ℝ), quarterGammaDensity644 v * Real.exp (-c * |v - z|)

/-- The positive-support convolution is integrable for nonnegative decay
rate. Its kernel is bounded by one and the fifth exponential moment supplies
an integrable majorant. -/
theorem quarter_gamma_conv_integrable_644 (z : ℝ) {c : ℝ} (hc : 0 ≤ c) :
    MeasureTheory.IntegrableOn (fun v : ℝ ↦ quarterGammaDensity644 v * Real.exp (-c * |v - z|))
      (Set.Ioi 0) := by
  have hi' :
    MeasureTheory.IntegrableOn (fun v : ℝ ↦ v ^ 5 * Real.exp (-(107 / 100 : ℝ) * v)) (Set.Ioi 0) :=
    Analysis.exponential_moment_integrable (by norm_num only) 5
  let f : ℝ → ℝ := fun v ↦
    ((107 / 100 : ℝ) ^ 5 / 120) * v ^ 5 * Real.exp (-(107 / 100 : ℝ) * v) * Real.exp (-c * |v - z|)
  have hcont : Continuous f := by
    dsimp only [f]
    fun_prop
  have hmajor := hi'.const_mul ((107 / 100 : ℝ) ^ 5 / 120)
  have hf : MeasureTheory.IntegrableOn f (Set.Ioi 0) := by
    refine hmajor.mono' (hcont.continuousOn.aestronglyMeasurable measurableSet_Ioi) ?_
    apply MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi
    intro v hv
    have hvpos : 0 < v := hv
    have hbase : 0 ≤ ((107 / 100 : ℝ) ^ 5 / 120) * v ^ 5 * Real.exp (-(107 / 100 : ℝ) * v) := by
      positivity
    have he : Real.exp (-c * |v - z|) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc) (abs_nonneg _))
    dsimp only [f]
    rw [Real.norm_of_nonneg (mul_nonneg hbase (Real.exp_pos _).le)]
    simpa only [mul_assoc] using mul_le_of_le_one_right hbase he
  apply hf.congr_fun _ measurableSet_Ioi
  intro v hv
  dsimp only [f, quarterGammaDensity644]
  rw [ite_eq_left hv.le]

/-- The real part of the normalized positive-pole resolvent equals its
positive-half-line density convolution, with the exact factors of `c` and
`2π`. Integrability justifies moving the real embedding through the integral. -/
theorem quarter_gamma_pole_real_644 (y : ℝ) {c : ℝ} (hc : 0 < c) :
    (1 / (2 * Real.pi)) * c ^ 2 *
        (∫ t : ℝ,
            (quarterKernel644.function (Complex.I * t) * Complex.exp (Complex.I * (t : ℂ) * y)) *
              ((1 / (c ^ 2 + t ^ 2) : ℝ) : ℂ)).re =
      (c / 2) * quarterGammaConvolution644 (y + 2687 / 1000) c := by
  have h := quarter_pole_density_pos_644 y hc
  have hi := quarter_gamma_conv_integrable_644 (y + 2687 / 1000) hc.le
  have hcast := Complex.ofRealCLM.integral_comp_comm hi
  change
    (∫ v in Set.Ioi (0 : ℝ),
        ((quarterGammaDensity644 v * Real.exp (-c * |v - (y + 2687 / 1000)|) : ℝ) : ℂ)) =
      ((quarterGammaConvolution644 (y + 2687 / 1000) c : ℝ) : ℂ) at hcast
  simp only [Complex.ofReal_mul] at hcast
  rw [hcast] at h
  have hr := congrArg Complex.re h
  simpa only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    mul_zero, add_zero, sub_zero] using hr

/-- The part of the convolution on `(0, z]` is a lower bound for the whole
convolution when the decay rate is nonnegative. On this interval the absolute
value simplifies to `z - v`, preparing the first-pole estimate. -/
theorem quarter_gamma_conv_lower_644 {z c : ℝ} (hc : 0 ≤ c) :
    (∫ v in Set.Ioc (0 : ℝ) z, quarterGammaDensity644 v * Real.exp (-c * (z - v))) ≤
      quarterGammaConvolution644 z c := by
  have hi := quarter_gamma_conv_integrable_644 z hc
  have hn : ∀ v : ℝ, 0 ≤ quarterGammaDensity644 v * Real.exp (-c * |v - z|) := by
    intro v
    have hd : 0 ≤ quarterGammaDensity644 v := by
      by_cases hv : 0 ≤ v
      · rw [quarterGammaDensity644, ite_eq_left hv]
        positivity
      · rw [quarterGammaDensity644, ite_eq_right hv]
    exact mul_nonneg hd (Real.exp_pos _).le
  have hb :=
    MeasureTheory.setIntegral_mono_set hi (Filter.Eventually.of_forall hn)
      (Filter.Eventually.of_forall (fun v (hv : v ∈ Set.Ioc (0 : ℝ) z) ↦ hv.1))
  have he :
    (∫ v in Set.Ioc (0 : ℝ) z, quarterGammaDensity644 v * Real.exp (-c * |v - z|)) =
      ∫ v in Set.Ioc (0 : ℝ) z, quarterGammaDensity644 v * Real.exp (-c * (z - v)) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
    intro v hv
    dsimp only
    rw [abs_of_nonpos (sub_nonpos.mpr hv.2), neg_sub]
  change _ ≤ quarterGammaConvolution644 z c
  rw [← he]
  exact hb

/-- On the initial interval, the density and pole exponential combine into
one fifth exponential moment with rate `27/25 - c`. The scale-dependent
factor is constant and can be evaluated separately. -/
theorem quarter_gamma_initial_644 (z c : ℝ) :
    (∫ v in Set.Ioc (0 : ℝ) z, quarterGammaDensity644 v * Real.exp (-c * (z - v))) =
      (((107 / 100 : ℝ) ^ 5 / 120) * Real.exp (-c * z)) *
        ∫ v in Set.Ioc (0 : ℝ) z, v ^ 5 * Real.exp (-((107 / 100 : ℝ) - c) * v) := by
  rw [← MeasureTheory.integral_const_mul]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
  intro v hv
  dsimp only
  rw [quarterGammaDensity644, ite_eq_left hv.1.le]
  have he : -(107 / 100 : ℝ) * v + -c * (z - v) = -c * z + -((107 / 100 : ℝ) - c) * v := by ring
  have hexp :
    Real.exp (-(107 / 100 : ℝ) * v) * Real.exp (-c * (z - v)) =
      Real.exp (-c * z) * Real.exp (-((107 / 100 : ℝ) - c) * v) := by
    rw [← Real.exp_add, he, Real.exp_add]
  have hm := congrArg (fun x : ℝ ↦ ((107 / 100 : ℝ) ^ 5 / 120) * v ^ 5 * x) hexp
  nlinarith only [hm]

/-- The first even-Gamma pole of the main kernel contributes at least
the certified truncated moment when the shifted logarithm is nonnegative. -/
theorem quarter_first_resolvent_644 {y : ℝ} (hy : 0 ≤ y + 2687 / 1000) :
    quarterGammaFirst644 (y + 2687 / 1000) ≤
      (1 / (2 * Real.pi)) *
        (∫ t : ℝ,
            (quarterKernel644.function (Complex.I * t) * Complex.exp (Complex.I * (t : ℂ) * y)) *
              ((1 / (1 / 4 + t ^ 2) : ℝ) : ℂ)).re := by
  have h :=
    quarter_gamma_conv_lower_644 (z := y + 2687 / 1000) (c := (1 / 2 : ℝ)) (by norm_num only)
  rw [quarter_gamma_initial_644] at h
  have hd : (107 / 100 : ℝ) - 1 / 2 = 57 / 100 := by norm_num only
  rw [hd, Analysis.exponential_moment_interval_ne (by norm_num only) hy 5] at h
  rw [quarter_gamma_first_closed_644 hy]
  have he := quarter_gamma_pole_real_644 y (c := (1 / 2 : ℝ)) (by norm_num only)
  norm_num only at h he ⊢
  nlinarith only [h, he]

/-- The first even-Gamma resolvent of the section 122 main kernel is
at least 0.02712 throughout the four certified comparison intervals. -/
theorem quarter_first_resolvent_rows_644 {r : ℝ} (hr : r ∈ Set.Icc 316 322) :
    0.02712 ≤
      (1 / (2 * Real.pi)) *
        (∫ t : ℝ,
            (quarterKernel644.function (Complex.I * t) *
                Complex.exp (Complex.I * (t : ℂ) * (2 * Real.log r : ℝ))) *
              ((1 / (1 / 4 + t ^ 2) : ℝ) : ℂ)).re := by
  have hr₁ : 1 ≤ r := by linarith only [hr.1]
  have hz : 0 ≤ 2 * Real.log r + 2687 / 1000 := by linarith only [Real.log_nonneg hr₁]
  have h := quarter_gamma_first_rows_644 hr
  rw [add_comm (2687 / 1000 : ℝ)] at h
  exact h.trans (quarter_first_resolvent_644 hz)

/-- For nonnegative shift and pole parameter, split the Gamma convolution at the shift.
Absolute-value simplification gives the left and right exponential integrals. -/
theorem quarter_gamma_conv_split_644 {z c : ℝ} (hz : 0 ≤ z) (hc : 0 ≤ c) :
    quarterGammaConvolution644 z c =
      (∫ v in Set.Ioc (0 : ℝ) z, quarterGammaDensity644 v * Real.exp (-c * (z - v))) +
        ∫ v in Set.Ioi z, quarterGammaDensity644 v * Real.exp (-c * (v - z)) := by
  have hi := quarter_gamma_conv_integrable_644 z hc
  have hi1 := hi.mono_set (Set.Ioc_subset_Ioi_self : Set.Ioc (0 : ℝ) z ⊆ Set.Ioi 0)
  have hi2 := hi.mono_set (Set.Ioi_subset_Ioi hz)
  have he1 :
    (∫ v in Set.Ioc (0 : ℝ) z, quarterGammaDensity644 v * Real.exp (-c * |v - z|)) =
      ∫ v in Set.Ioc (0 : ℝ) z, quarterGammaDensity644 v * Real.exp (-c * (z - v)) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
    intro v hv
    dsimp only
    rw [abs_of_nonpos (sub_nonpos.mpr hv.2), neg_sub]
  have he2 :
    (∫ v in Set.Ioi z, quarterGammaDensity644 v * Real.exp (-c * |v - z|)) =
      ∫ v in Set.Ioi z, quarterGammaDensity644 v * Real.exp (-c * (v - z)) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro v hv
    dsimp only
    rw [abs_of_nonneg (sub_nonneg.mpr hv.le)]
  unfold quarterGammaConvolution644
  rw [← Set.Ioc_union_Ioi_eq_Ioi hz,
    MeasureTheory.setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi hi1 hi2, he1, he2]

/-- For nonnegative shift and pole rate, the upper half of the convolution is the
closed fifth exponential tail. This supplies the right contribution in the pole estimate. -/
theorem quarter_gamma_right_moment_644 {z c : ℝ} (hz : 0 ≤ z) (hc : 0 ≤ c) :
    (∫ v in Set.Ioi z, quarterGammaDensity644 v * Real.exp (-c * (v - z))) =
      (((107 / 100 : ℝ) ^ 5 / 120) * Real.exp (-(107 / 100 : ℝ) * z)) *
        Analysis.logPowerTailPoly (c + 107 / 100) 5 z := by
  have hr : 0 < c + (107 / 100 : ℝ) := by linarith only [hc]
  have he :
    (∫ v in Set.Ioi z, quarterGammaDensity644 v * Real.exp (-c * (v - z))) =
      ∫ v in Set.Ioi z,
        (((107 / 100 : ℝ) ^ 5 / 120) * Real.exp (c * z)) *
          (v ^ 5 * Real.exp (-(c + 107 / 100) * v)) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro v hv
    dsimp only
    rw [quarterGammaDensity644, ite_eq_left (hz.trans hv.le)]
    rw [mul_assoc _ (Real.exp _) (Real.exp _), ← Real.exp_add]
    have hexp : -(107 / 100 : ℝ) * v + -c * (v - z) = c * z + -(c + 107 / 100) * v := by ring
    rw [hexp, Real.exp_add]
    ring
  rw [he, MeasureTheory.integral_const_mul, Analysis.exponential_moment_tail hr hz 5]
  rw [mul_assoc ((107 / 100 : ℝ) ^ 5 / 120), ← mul_assoc (Real.exp _) (Real.exp _), ← Real.exp_add]
  have hexp : c * z + -(c + 107 / 100) * z = -(107 / 100 : ℝ) * z := by ring
  rw [hexp, mul_assoc]

/-- For a nonnegative shift and pole rate, express the Gamma convolution as an initial
moment plus its closed upper tail. This prepares the higher-pole comparison. -/
theorem quarter_gamma_conv_moments_644 {z c : ℝ} (hz : 0 ≤ z) (hc : 0 ≤ c) :
    quarterGammaConvolution644 z c =
      (((107 / 100 : ℝ) ^ 5 / 120) * Real.exp (-c * z)) *
          (∫ v in Set.Ioc (0 : ℝ) z, v ^ 5 * Real.exp (-((107 / 100 : ℝ) - c) * v)) +
        (((107 / 100 : ℝ) ^ 5 / 120) * Real.exp (-(107 / 100 : ℝ) * z)) *
          Analysis.logPowerTailPoly (c + 107 / 100) 5 z := by
  rw [quarter_gamma_conv_split_644 hz hc, quarter_gamma_initial_644,
    quarter_gamma_right_moment_644 hz hc]

/-- For a nonnegative shift and nonnegative pole rate different from the profile rate,
evaluate both halves of the Gamma convolution in closed form. -/
theorem quarter_gamma_conv_closed_644 {z c : ℝ} (hz : 0 ≤ z) (hc : 0 ≤ c)
    (hne : c ≠ (107 / 100 : ℝ)) :
    quarterGammaConvolution644 z c =
      (((107 / 100 : ℝ) ^ 5 / 120) * Real.exp (-c * z)) *
          (Analysis.logPowerTailPoly (107 / 100 - c) 5 0 -
            Real.exp (-((107 / 100 : ℝ) - c) * z) * Analysis.logPowerTailPoly (107 / 100 - c) 5 z) +
        (((107 / 100 : ℝ) ^ 5 / 120) * Real.exp (-(107 / 100 : ℝ) * z)) *
          Analysis.logPowerTailPoly (c + 107 / 100) 5 z := by
  have hr : (107 / 100 : ℝ) - c ≠ 0 := sub_ne_zero.mpr hne.symm
  rw [quarter_gamma_conv_moments_644 hz hc, Analysis.exponential_moment_interval_ne hr hz 5]

/-- For every later Gamma pole, separate the closed convolution into its polynomial
part and the positive exponential endpoint term. -/
theorem quarter_gamma_conv_expansion_644 {z c : ℝ} (hz : 0 ≤ z) (hc : 0 ≤ c)
    (hne : c ≠ (107 / 100 : ℝ)) :
    quarterGammaConvolution644 z c =
      (((107 / 100 : ℝ) ^ 5 / 120) * Real.exp (-(107 / 100 : ℝ) * z)) *
          (Analysis.logPowerTailPoly (c + 107 / 100) 5 z -
            Analysis.logPowerTailPoly (107 / 100 - c) 5 z) +
        (((107 / 100 : ℝ) ^ 5 / 120) * Real.exp (-c * z)) *
          Analysis.logPowerTailPoly (107 / 100 - c) 5 0 := by
  rw [quarter_gamma_conv_closed_644 hz hc hne]
  have hexp :
    Real.exp (-c * z) * Real.exp (-((107 / 100 : ℝ) - c) * z) =
      Real.exp (-(107 / 100 : ℝ) * z) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [← hexp]
  ring

/-- The first resolvent convolution is the truncated first-pole moment
plus the exact forward polynomial contribution. -/
theorem quarter_first_conv_split_644 {z : ℝ} (hz : 0 ≤ z) :
    quarterGammaConvolution644 z (1 / 2) =
      quarterGammaFirst644 z +
        ((107 / 100 : ℝ) ^ 5 / 120 * Real.exp (-(107 / 100) * z)) *
          Analysis.logPowerTailPoly (157 / 100) 5 z := by
  rw [quarter_gamma_conv_closed_644 hz (by norm_num only) (by norm_num only),
    quarter_gamma_first_closed_644 hz]
  norm_num only

/-- The forward first-pole polynomial covers the constant and odd-order
corrections left by summing the later poles. -/
theorem quarter_first_forward_lower_644 {z : ℝ} (hz : 0 ≤ z) :
    z ^ 5 / (157 / 100) + 5 * z ^ 4 / (157 / 100) ^ 2 + 60 * z ^ 2 / (157 / 100) ^ 4 +
        120 / (157 / 100) ^ 6 ≤
      Analysis.logPowerTailPoly (157 / 100) 5 z := by
  norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat, Nat.cast_one]
  nlinarith only [pow_nonneg hz 3, hz]

end PseudoPrime.PrimeTestBounds.MillerRabin
