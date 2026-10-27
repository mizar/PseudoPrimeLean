/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Analysis.Real.Pi.Bounds
public import PseudoPrime.Analysis.ComplexExponentialBounds
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.PreSiftedLargeSieve

/-!
# Pre-sifted hybrid large-sieve localization

This module constructs the fixed smooth window used to pass from the short-interval pre-sifted
large sieve to its height-integrated hybrid form.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity

/--
Definition: the real one-dimensional bump centered at zero with inner radius `1/2` and outer
radius `1`.

Role: provides the fixed smooth profile used for localization on the logarithmic axis.
-/
noncomputable def preSiftedHybridUnitBump : ContDiffBump (0 : ℝ) :=
  { rIn := 1 / 2
    rOut := 1
    rIn_pos := by norm_num only [one_div]
    rIn_lt_rOut := by norm_num only [one_div] }

/--
Definition: the unit-mass normalization of `preSiftedHybridUnitBump` with respect to Lebesgue
measure on `ℝ`.

Output: a nonnegative smooth window supported in the unit ball.

Role: its scale changes will provide the compactly supported kernel in the hybrid mean-square
localization.
-/
noncomputable def preSiftedHybridUnitWindow : ℝ → ℝ :=
  preSiftedHybridUnitBump.normed MeasureTheory.volume

/--
Definition: the Schwartz-map packaging of `preSiftedHybridUnitWindow`.

Proof: a compactly supported smooth function defines a Schwartz map.

Role: lets the hybrid localization use the existing Schwartz–Plancherel theorem.
-/
noncomputable def preSiftedHybridUnitWindowComplex : ℝ → ℂ := fun x =>
  Complex.ofRealCLM (preSiftedHybridUnitWindow x)

/--
Definition: the complex Schwartz-map packaging of the real-valued unit window.

Proof: postcompose the smooth bump with the complexification map, which preserves compact
support and smoothness.

Role: provides the complex-valued Fourier transform used in the height localization.
-/
noncomputable def preSiftedHybridUnitWindowSchwartz : SchwartzMap ℝ ℂ :=
  (ContDiffBump.hasCompactSupport_normed (μ := MeasureTheory.volume)
          preSiftedHybridUnitBump).comp_left
      (Complex.ofRealCLM.map_zero) |>.toSchwartzMap
    (ContDiff.continuousLinearMap_comp Complex.ofRealCLM
      (ContDiffBump.contDiff_normed (μ := MeasureTheory.volume) (n := ⊤) preSiftedHybridUnitBump))

/--
Claim: the underlying function of the Schwartz window is the normalized bump window.

Proof: `HasCompactSupport.toSchwartzMap` preserves the underlying function.

Role: connects pointwise kernel formulas to the Fourier transform on Schwartz maps.
-/
theorem coe_preSiftedHybridUnitWindowSchwartz :
    (preSiftedHybridUnitWindowSchwartz : ℝ → ℂ) = preSiftedHybridUnitWindowComplex :=
  rfl

/--
Claim: the Fourier transform of a complex Schwartz map on `ℝ` has the exponential integral
representation used by the hybrid Dirichlet polynomial.

Input: a complex-valued Schwartz map and a real frequency.

Proof: apply mathlib's real Fourier integral formula and convert scalar multiplication on `ℂ` to
complex multiplication.

Role: provides the common Fourier representation for the unit window and its dilations.
-/
theorem preSiftedHybrid_fourier_eq_integral_exp (f : SchwartzMap ℝ ℂ) (ξ : ℝ) :
    (FourierTransform.fourier f : ℝ → ℂ) ξ =
      ∫ x : ℝ, Complex.exp ((-2 * Real.pi * x * ξ) * Complex.I) * f x ∂MeasureTheory.volume := by
  change FourierTransform.fourier (f : ℝ → ℂ) ξ = _
  calc
    FourierTransform.fourier (f : ℝ → ℂ) ξ =
        ∫ x : ℝ, Complex.exp (↑(-2 * Real.pi * x * ξ) * Complex.I) • f x ∂MeasureTheory.volume :=
      Real.fourier_real_eq_integral_exp_smul (f : ℝ → ℂ) ξ
    _ = ∫ x : ℝ, Complex.exp ((-2 * Real.pi * x * ξ) * Complex.I) * f x ∂MeasureTheory.volume := by
      congr 1
      funext x
      rw [smul_eq_mul]
      congr 1
      congr 1
      push_cast
      ring

/--
Claim: the Fourier transform of the Schwartz window is represented by the usual integral formula.

Proof: identify the Schwartz Fourier transform with the real Fourier integral and convert the
real scalar action on `ℂ` to multiplication.

Role: exposes the integral formula needed to estimate the transform near frequency zero.
-/
theorem preSiftedHybridUnitWindowSchwartz_fourier_eq_integral (ξ : ℝ) :
    (FourierTransform.fourier preSiftedHybridUnitWindowSchwartz : ℝ → ℂ) ξ =
      ∫ x : ℝ,
        Complex.exp ((-2 * Real.pi * x * ξ) * Complex.I) *
          preSiftedHybridUnitWindowComplex x ∂MeasureTheory.volume := by
  calc
    (FourierTransform.fourier preSiftedHybridUnitWindowSchwartz : ℝ → ℂ) ξ =
        ∫ x : ℝ,
          Complex.exp ((-2 * Real.pi * x * ξ) * Complex.I) *
            (preSiftedHybridUnitWindowSchwartz : ℝ → ℂ) x ∂MeasureTheory.volume :=
      preSiftedHybrid_fourier_eq_integral_exp preSiftedHybridUnitWindowSchwartz ξ
    _ =
        ∫ x : ℝ,
          Complex.exp ((-2 * Real.pi * x * ξ) * Complex.I) *
            preSiftedHybridUnitWindowComplex x ∂MeasureTheory.volume :=
      by simp only [coe_preSiftedHybridUnitWindowSchwartz]

/--
Claim: the exponential factor in the real Fourier kernel differs from one by at most its phase
size.

Proof: apply the left-half-plane exponential estimate to the purely imaginary phase and compute
its complex norm.

Role: bounds the Fourier transform's deviation from its value at frequency zero.
-/
theorem norm_preSiftedHybridFourierPhase_sub_one_le (x ξ : ℝ) :
    ‖Complex.exp ((((-2 * Real.pi * x * ξ : ℝ) : ℂ) * Complex.I)) - 1‖ ≤
      2 * Real.pi * |ξ| * |x| := by
  have hz : ((((-2 * Real.pi * x * ξ : ℝ) : ℂ) * Complex.I).re) ≤ 0 := by
    rw [Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
      sub_zero]
    exact le_rfl
  have h := PseudoPrime.Analysis.norm_exp_sub_one_le_of_re_nonpos hz
  have hcoef : |(-2 : ℝ) * Real.pi| = 2 * Real.pi := by
    rw [abs_mul, abs_of_neg (by norm_num), abs_of_pos Real.pi_pos]
    norm_num
  have hscalar : ‖((-2 * Real.pi * x * ξ : ℝ) : ℂ)‖ = 2 * Real.pi * |ξ| * |x| := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul, hcoef]
    ring
  calc
    ‖Complex.exp ((((-2 * Real.pi * x * ξ : ℝ) : ℂ) * Complex.I)) - 1‖ ≤
        ‖((-2 * Real.pi * x * ξ : ℝ) : ℂ) * Complex.I‖ :=
      h
    _ = ‖((-2 * Real.pi * x * ξ : ℝ) : ℂ)‖ * ‖Complex.I‖ := norm_mul _ _
    _ = 2 * Real.pi * |ξ| * |x| := by rw [hscalar, Complex.norm_I, mul_one]

/--
Claim: the normalized hybrid window has integral one.

Proof: use the normalization identity for `ContDiffBump.normed`.

Role: fixes the mass of every rescaled localization kernel.
-/
theorem integral_preSiftedHybridUnitWindow :
    ∫ x : ℝ, preSiftedHybridUnitWindow x ∂MeasureTheory.volume = 1 :=
  ContDiffBump.integral_normed preSiftedHybridUnitBump

/--
Claim: the normalized hybrid window vanishes outside the open unit ball.

Proof: identify its support with the bump's unit ball and use the support characterization of a
function.

Role: restricts the phase error in the Fourier integral to points with absolute value at most one.
-/
theorem preSiftedHybridUnitWindow_eq_zero_of_one_le_abs {x : ℝ} (hx : 1 ≤ |x|) :
    preSiftedHybridUnitWindow x = 0 := by
  have hsupp : Function.support preSiftedHybridUnitWindow = Metric.ball 0 1 := by
    change Function.support (preSiftedHybridUnitBump.normed MeasureTheory.volume) = Metric.ball 0 1
    simpa only [preSiftedHybridUnitBump] using
      (ContDiffBump.support_normed_eq (f := preSiftedHybridUnitBump) (μ := MeasureTheory.volume))
  have hxnot : x ∉ Function.support preSiftedHybridUnitWindow := by
    rw [hsupp]
    simp only [Metric.mem_ball, Real.dist_eq]
    exact not_lt.mpr (by simpa only [Real.norm_eq_abs, sub_zero] using hx)
  by_contra hne
  exact hxnot (Function.mem_support.mpr hne)

/--
Claim: the normalized hybrid window is pointwise nonnegative.

Proof: use nonnegativity of the normalized bump.

Role: permits pointwise comparison of its square with the window itself.
-/
theorem preSiftedHybridUnitWindow_nonneg (x : ℝ) : 0 ≤ preSiftedHybridUnitWindow x :=
  ContDiffBump.nonneg_normed preSiftedHybridUnitBump x

/--
Claim: the Fourier transform of the unit window differs from one by at most `2π |ξ|`.

Proof: subtract the unit mass inside the integral, bound the phase error on the unit support, and
integrate against the nonnegative unit-mass window.

Role: gives a uniform positive lower bound for the Fourier transform at sufficiently small
frequencies.
-/
theorem norm_preSiftedHybridUnitWindow_fourier_sub_one_le (ξ : ℝ) :
    ‖(FourierTransform.fourier preSiftedHybridUnitWindowSchwartz : ℝ → ℂ) ξ - 1‖ ≤
      2 * Real.pi * |ξ| := by
  let phase : ℝ → ℂ := fun x => Complex.exp ((((-2 * Real.pi * x * ξ : ℝ) : ℂ) * Complex.I))
  have hcomplex :
    MeasureTheory.Integrable preSiftedHybridUnitWindowComplex MeasureTheory.volume := by
    rw [← coe_preSiftedHybridUnitWindowSchwartz]
    exact preSiftedHybridUnitWindowSchwartz.integrable
  have hreal : MeasureTheory.Integrable preSiftedHybridUnitWindow MeasureTheory.volume :=
    ContDiffBump.integrable_normed preSiftedHybridUnitBump
  have hmass : ∫ x : ℝ, preSiftedHybridUnitWindowComplex x ∂MeasureTheory.volume = 1 := by
    change ∫ x : ℝ, Complex.ofRealCLM (preSiftedHybridUnitWindow x) ∂MeasureTheory.volume = 1
    rw [ContinuousLinearMap.integral_comp_comm _ hreal]
    rw [integral_preSiftedHybridUnitWindow]
    rfl
  have hphaseNorm (x : ℝ) : ‖phase x‖ ≤ 1 := by
    dsimp [phase]
    have hre : ((((-2 * Real.pi * x * ξ : ℝ) : ℂ) * Complex.I).re) = 0 := by
      rw [Complex.mul_re]
      simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
        zero_mul, sub_zero]
    rw [Complex.norm_exp, hre]
    norm_num only [Real.exp_zero]
  have hphaseCont : Continuous phase := by
    dsimp [phase]
    fun_prop
  have hmul :
    MeasureTheory.Integrable (fun x : ℝ => phase x * preSiftedHybridUnitWindowComplex x)
      MeasureTheory.volume :=
    hcomplex.bdd_mul hphaseCont.aestronglyMeasurable (Filter.Eventually.of_forall hphaseNorm)
  have hdiff :
    MeasureTheory.Integrable (fun x : ℝ => (phase x - 1) * preSiftedHybridUnitWindowComplex x)
      MeasureTheory.volume := by
    have hsub :
      MeasureTheory.Integrable
        (fun x : ℝ =>
          phase x * preSiftedHybridUnitWindowComplex x - preSiftedHybridUnitWindowComplex x)
        MeasureTheory.volume :=
      hmul.sub hcomplex
    apply hsub.congr
    filter_upwards [] with x
    simp only [sub_mul, one_mul]
  have hC : 0 ≤ 2 * Real.pi * |ξ| :=
    mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) (abs_nonneg ξ)
  have hpoint (x : ℝ) :
    ‖(phase x - 1) * preSiftedHybridUnitWindowComplex x‖ ≤
      (2 * Real.pi * |ξ|) * preSiftedHybridUnitWindow x := by
    by_cases hx : 1 ≤ |x|
    · change
        ‖(phase x - 1) * (preSiftedHybridUnitWindow x : ℂ)‖ ≤
          (2 * Real.pi * |ξ|) * preSiftedHybridUnitWindow x
      rw [preSiftedHybridUnitWindow_eq_zero_of_one_le_abs hx]
      simp only [Complex.ofReal_zero, mul_zero, norm_zero]
      exact le_rfl
    · have hxlt : |x| < 1 := lt_of_not_ge hx
      have hφ : 0 ≤ preSiftedHybridUnitWindow x := preSiftedHybridUnitWindow_nonneg x
      calc
        ‖(phase x - 1) * preSiftedHybridUnitWindowComplex x‖ =
            ‖phase x - 1‖ * preSiftedHybridUnitWindow x :=
          by
          change ‖(phase x - 1) * (preSiftedHybridUnitWindow x : ℂ)‖ = _
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hφ]
        _ ≤ (2 * Real.pi * |ξ| * |x|) * preSiftedHybridUnitWindow x :=
          mul_le_mul_of_nonneg_right (norm_preSiftedHybridFourierPhase_sub_one_le x ξ) hφ
        _ ≤ (2 * Real.pi * |ξ|) * preSiftedHybridUnitWindow x := by
          calc
            _ ≤ ((2 * Real.pi * |ξ|) * 1) * preSiftedHybridUnitWindow x :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hxlt.le hC) hφ
            _ = (2 * Real.pi * |ξ|) * preSiftedHybridUnitWindow x := by rw [mul_one]
        _ = (2 * Real.pi * |ξ|) * preSiftedHybridUnitWindow x := by ring
  have hnorm :
    ‖∫ x : ℝ, (phase x - 1) * preSiftedHybridUnitWindowComplex x ∂MeasureTheory.volume‖ ≤
      2 * Real.pi * |ξ| := by
    calc
      ‖∫ x : ℝ, (phase x - 1) * preSiftedHybridUnitWindowComplex x ∂MeasureTheory.volume‖ ≤
          ∫ x : ℝ, ‖(phase x - 1) * preSiftedHybridUnitWindowComplex x‖ ∂MeasureTheory.volume :=
        MeasureTheory.norm_integral_le_integral_norm _
      _ ≤ ∫ x : ℝ, (2 * Real.pi * |ξ|) * preSiftedHybridUnitWindow x ∂MeasureTheory.volume :=
        MeasureTheory.integral_mono_ae hdiff.norm (hreal.const_mul (2 * Real.pi * |ξ|))
          (Filter.Eventually.of_forall hpoint)
      _ = 2 * Real.pi * |ξ| := by
        rw [MeasureTheory.integral_const_mul, integral_preSiftedHybridUnitWindow]
        simp only [mul_one]
  have hrepr :
    (FourierTransform.fourier preSiftedHybridUnitWindowSchwartz : ℝ → ℂ) ξ - 1 =
      ∫ x : ℝ, (phase x - 1) * preSiftedHybridUnitWindowComplex x ∂MeasureTheory.volume := by
    calc
      _ =
          (∫ x : ℝ, phase x * preSiftedHybridUnitWindowComplex x ∂MeasureTheory.volume) -
            ∫ x : ℝ, preSiftedHybridUnitWindowComplex x ∂MeasureTheory.volume :=
        by
        rw [preSiftedHybridUnitWindowSchwartz_fourier_eq_integral]
        rw [hmass]
        congr 1
        apply MeasureTheory.integral_congr_ae
        filter_upwards [] with x
        dsimp [phase]
        congr 2
        push_cast
        ring
      _ =
          ∫ x : ℝ,
            (phase x * preSiftedHybridUnitWindowComplex x -
              preSiftedHybridUnitWindowComplex x) ∂MeasureTheory.volume :=
        (MeasureTheory.integral_sub hmul hcomplex).symm
      _ = ∫ x : ℝ, (phase x - 1) * preSiftedHybridUnitWindowComplex x ∂MeasureTheory.volume := by
        congr 1
        funext x
        ring
  rw [hrepr]
  exact hnorm

/--
Claim: the unit-window Fourier transform has norm at least `1/2` when its phase error is at most
`1/4`.

Proof: combine the preceding deviation estimate with the triangle inequality and the unit norm of
one.

Role: supplies the nonvanishing Fourier factor needed in the height localization.
-/
theorem norm_preSiftedHybridUnitWindow_fourier_ge_half {ξ : ℝ} (hξ : 2 * Real.pi * |ξ| ≤ 1 / 4) :
    (1 / 2 : ℝ) ≤ ‖(FourierTransform.fourier preSiftedHybridUnitWindowSchwartz : ℝ → ℂ) ξ‖ := by
  have hdev := norm_preSiftedHybridUnitWindow_fourier_sub_one_le ξ
  have hdev' :
    ‖(FourierTransform.fourier preSiftedHybridUnitWindowSchwartz : ℝ → ℂ) ξ - 1‖ ≤ 1 / 4 :=
    hdev.trans hξ
  have hrev :
    ‖(1 : ℂ) - (FourierTransform.fourier preSiftedHybridUnitWindowSchwartz : ℝ → ℂ) ξ‖ =
      ‖(FourierTransform.fourier preSiftedHybridUnitWindowSchwartz : ℝ → ℂ) ξ - 1‖ := by
    rw [show
        (1 : ℂ) - (FourierTransform.fourier preSiftedHybridUnitWindowSchwartz : ℝ → ℂ) ξ =
          -((FourierTransform.fourier preSiftedHybridUnitWindowSchwartz : ℝ → ℂ) ξ - 1)
        by ring]
    rw [norm_neg]
  have htri :
    ‖(1 : ℂ)‖ ≤
      ‖(1 : ℂ) - (FourierTransform.fourier preSiftedHybridUnitWindowSchwartz : ℝ → ℂ) ξ‖ +
        ‖(FourierTransform.fourier preSiftedHybridUnitWindowSchwartz : ℝ → ℂ) ξ‖ := by
    calc
      ‖(1 : ℂ)‖ =
          ‖((1 : ℂ) - (FourierTransform.fourier preSiftedHybridUnitWindowSchwartz : ℝ → ℂ) ξ) +
              (FourierTransform.fourier preSiftedHybridUnitWindowSchwartz : ℝ → ℂ) ξ‖ :=
        by
        congr 1
        ring
      _ ≤
          ‖(1 : ℂ) - (FourierTransform.fourier preSiftedHybridUnitWindowSchwartz : ℝ → ℂ) ξ‖ +
            ‖(FourierTransform.fourier preSiftedHybridUnitWindowSchwartz : ℝ → ℂ) ξ‖ :=
        norm_add_le _ _
  rw [norm_one, hrev] at htri
  linarith only [htri, hdev']

/--
Claim: the normalized hybrid window is bounded above by one.

Proof: the inner closed ball has Lebesgue measure one, so the normalized bump's inner-radius
bound is one.

Role: gives the unit-scale pointwise bound needed for the kernel's squared integral estimate.
-/
theorem preSiftedHybridUnitWindow_le_one (x : ℝ) : preSiftedHybridUnitWindow x ≤ 1 := by
  have hvol : MeasureTheory.volume.real (Metric.closedBall (0 : ℝ) (1 / 2)) = 1 := by
    change (MeasureTheory.volume (Metric.closedBall (0 : ℝ) (1 / 2))).toReal = 1
    rw [Real.volume_closedBall]
    rw [ENNReal.toReal_ofReal (by norm_num only [one_div])]
    norm_num only [one_div]
  calc
    preSiftedHybridUnitWindow x ≤
        1 / MeasureTheory.volume.real (Metric.closedBall (0 : ℝ) preSiftedHybridUnitBump.rIn) :=
      ContDiffBump.normed_le_div_measure_closedBall_rIn preSiftedHybridUnitBump MeasureTheory.volume
        x
    _ = 1 := by
      rw [show preSiftedHybridUnitBump.rIn = 1 / 2 from rfl, hvol]
      norm_num only [one_div]

/--
Claim: the squared hybrid window is integrable and has integral at most one.

Proof: its pointwise square is bounded by the nonnegative unit-mass window, and integrability
follows by domination.

Role: supplies the scale-independent squared-mass bound for localization.
-/
theorem integral_sq_preSiftedHybridUnitWindow_le_one :
    ∫ x : ℝ, preSiftedHybridUnitWindow x ^ 2 ∂MeasureTheory.volume ≤ 1 := by
  have hcont : Continuous preSiftedHybridUnitWindow := by
    change Continuous (preSiftedHybridUnitBump.normed MeasureTheory.volume)
    exact
      ContDiff.continuous
        (ContDiffBump.contDiff_normed (μ := MeasureTheory.volume) (n := ⊤) preSiftedHybridUnitBump)
  have hint : MeasureTheory.Integrable preSiftedHybridUnitWindow MeasureTheory.volume :=
    ContDiffBump.integrable_normed preSiftedHybridUnitBump
  have hsqIntegrable :
    MeasureTheory.Integrable (fun x : ℝ => preSiftedHybridUnitWindow x ^ 2)
      MeasureTheory.volume := by
    apply hint.mono' ((hcont.pow 2).aestronglyMeasurable)
    filter_upwards [] with x
    change |preSiftedHybridUnitWindow x ^ 2| ≤ preSiftedHybridUnitWindow x
    rw [abs_of_nonneg (sq_nonneg (preSiftedHybridUnitWindow x))]
    calc
      preSiftedHybridUnitWindow x ^ 2 = preSiftedHybridUnitWindow x * preSiftedHybridUnitWindow x :=
        by rw [pow_two]
      _ ≤ preSiftedHybridUnitWindow x * 1 :=
        mul_le_mul_of_nonneg_left (preSiftedHybridUnitWindow_le_one x)
          (preSiftedHybridUnitWindow_nonneg x)
      _ = preSiftedHybridUnitWindow x := mul_one _
  have hsqLe :
    (fun x : ℝ => preSiftedHybridUnitWindow x ^ 2) ≤ᵐ[MeasureTheory.volume]
      preSiftedHybridUnitWindow := by
    filter_upwards [] with x
    calc
      preSiftedHybridUnitWindow x ^ 2 = preSiftedHybridUnitWindow x * preSiftedHybridUnitWindow x :=
        by rw [pow_two]
      _ ≤ preSiftedHybridUnitWindow x * 1 :=
        mul_le_mul_of_nonneg_left (preSiftedHybridUnitWindow_le_one x)
          (preSiftedHybridUnitWindow_nonneg x)
      _ = preSiftedHybridUnitWindow x := mul_one _
  calc
    ∫ x : ℝ, preSiftedHybridUnitWindow x ^ 2 ∂MeasureTheory.volume ≤
        ∫ x : ℝ, preSiftedHybridUnitWindow x ∂MeasureTheory.volume :=
      MeasureTheory.integral_mono_ae hsqIntegrable hint hsqLe
    _ = 1 := integral_preSiftedHybridUnitWindow

/--
Definition: the dilation of the unit window at positive scale `δ`, given by
`δ⁻¹ * φ(δ⁻¹ x)`.

Output: a real-valued localization kernel on the logarithmic axis.

Role: its mass and squared mass control the height-integrated hybrid estimate.
-/
noncomputable def preSiftedHybridKernel (δ : ℝ) : ℝ → ℝ := fun x =>
  δ⁻¹ * preSiftedHybridUnitWindow (δ⁻¹ * x)

/--
Definition: the complex Schwartz-map packaging of the dilated hybrid kernel at positive scale.

Construction: compose the unit window with multiplication by `δ⁻¹` and multiply its values by
`δ⁻¹`.

Role: provides the scaled kernel to the Schwartz Fourier transform and Plancherel theorem.
-/
noncomputable def preSiftedHybridKernelSchwartz (δ : ℝ) (hδ : 0 < δ) : SchwartzMap ℝ ℂ :=
  let u : ℝˣ := Units.mk0 δ⁻¹ (inv_ne_zero (ne_of_gt hδ))
  δ⁻¹ •
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.unitsEquivAut ℝ u)
      preSiftedHybridUnitWindowSchwartz)

/--
Definition: translate a complex Schwartz map by `a`, giving the function `x ↦ f(x - a)`.

Construction: compose the Schwartz map with the translation isometry.

Role: packages each localized summand as a Schwartz function for finite sums and Plancherel.
-/
noncomputable def preSiftedHybridTranslateSchwartz (f : SchwartzMap ℝ ℂ) (a : ℝ) :
    SchwartzMap ℝ ℂ := by
  have hg : (fun x : ℝ => x - a).HasTemperateGrowth :=
    Function.HasTemperateGrowth.id.sub (Function.HasTemperateGrowth.const a)
  have hanti : AntilipschitzWith 1 (fun x : ℝ => x - a) := by
    convert (AffineIsometryEquiv.vaddConst ℝ (-a)).antilipschitzWith using 1
    ext x
    simp only [AffineIsometryEquiv.coe_vaddConst, vadd_eq_add]
    ring
  exact SchwartzMap.compCLMOfAntilipschitz ℂ hg hanti f

/--
Claim: the translated Schwartz map evaluates to `f (x - a)`.

Role: exposes the translated summand used in the finite Dirichlet polynomial localization.
-/
theorem coe_preSiftedHybridTranslateSchwartz (f : SchwartzMap ℝ ℂ) (a : ℝ) :
    (preSiftedHybridTranslateSchwartz f a : ℝ → ℂ) = fun x => (f : ℝ → ℂ) (x - a) := by
  funext x
  rfl

/--
Claim: translation multiplies a Schwartz map's Fourier transform by the corresponding phase.

Proof: apply the translation formula for the real Fourier integral to the underlying function.

Role: gives the Fourier factorization for each localized summand.
-/
theorem preSiftedHybridTranslateSchwartz_fourier (f : SchwartzMap ℝ ℂ) (a ξ : ℝ) :
    (FourierTransform.fourier (preSiftedHybridTranslateSchwartz f a) : ℝ → ℂ) ξ =
      Real.fourierChar ((-a) * ξ) • (FourierTransform.fourier f : ℝ → ℂ) ξ := by
  rw [SchwartzMap.fourier_coe, coe_preSiftedHybridTranslateSchwartz, SchwartzMap.fourier_coe]
  have h :=
    Fourier.fourierIntegral_comp_add_right Real.fourierChar MeasureTheory.volume (f : ℝ → ℂ) (-a)
  have hξ := congrFun h ξ
  simpa only [Real.fourier_real_eq, Fourier.fourierIntegral_def, sub_eq_add_neg,
    Function.comp_apply] using hξ

/--
Claim: evaluation commutes with a finite sum of scalar multiples of Schwartz maps.

Proof: induct on the finite index set and use the pointwise addition and scalar-action formulas.

Role: converts the finite Schwartz sum into the pointwise localized Dirichlet polynomial.
-/
theorem coe_sum_smul_preSiftedHybridSchwartz {ι : Type} (s : Finset ι) (c : ι → ℂ)
    (F : ι → SchwartzMap ℝ ℂ) (x : ℝ) :
    (∑ i ∈ s, c i • F i : SchwartzMap ℝ ℂ) x = ∑ i ∈ s, c i • (F i : ℝ → ℂ) x := by
  classical
    induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    rw [add_apply, smul_apply, ih]

/--
Claim: the Fourier transform of a finite sum of translated Schwartz maps is the sum of their
Fourier phases.

Proof: use linearity of the Schwartz Fourier transform and the translation formula termwise.

Role: factors the Fourier transform of the finite Dirichlet polynomial localized by the kernel.
-/
theorem preSiftedHybridTranslateSchwartz_sum_fourier {ι : Type} (s : Finset ι) (c : ι → ℂ)
    (a : ι → ℝ) (f : SchwartzMap ℝ ℂ) (ξ : ℝ) :
    (FourierTransform.fourier (∑ i ∈ s, c i • preSiftedHybridTranslateSchwartz f (a i)) : ℝ → ℂ) ξ =
      ∑ i ∈ s,
        c i • (Real.fourierChar ((-(a i)) * ξ) • (FourierTransform.fourier f : ℝ → ℂ) ξ) := by
  have hmap :
    FourierTransform.fourier (∑ i ∈ s, c i • preSiftedHybridTranslateSchwartz f (a i)) =
      ∑ i ∈ s, c i • FourierTransform.fourier (preSiftedHybridTranslateSchwartz f (a i)) := by
    change
      SchwartzMap.fourierTransformCLM ℂ (∑ i ∈ s, c i • preSiftedHybridTranslateSchwartz f (a i)) =
        ∑ i ∈ s, c i • SchwartzMap.fourierTransformCLM ℂ (preSiftedHybridTranslateSchwartz f (a i))
    rw [map_sum]
    simp only [map_smul]
  have hpoint := congrArg (fun g : SchwartzMap ℝ ℂ => (g : ℝ → ℂ) ξ) hmap
  rw [coe_sum_smul_preSiftedHybridSchwartz] at hpoint
  calc
    (FourierTransform.fourier (∑ i ∈ s, c i • preSiftedHybridTranslateSchwartz f (a i)) : ℝ → ℂ) ξ =
        ∑ i ∈ s,
          c i • (FourierTransform.fourier (preSiftedHybridTranslateSchwartz f (a i)) : ℝ → ℂ) ξ :=
      hpoint
    _ = ∑ i ∈ s, c i • (Real.fourierChar ((-(a i)) * ξ) • (FourierTransform.fourier f : ℝ → ℂ) ξ) :=
      by
      apply Finset.sum_congr rfl
      intro i hi
      rw [preSiftedHybridTranslateSchwartz_fourier]

/-- Translate the scaled kernel to a center `a` as the function `x ↦ κδ(x - a)`. -/
noncomputable def preSiftedHybridTranslatedKernelSchwartz (δ : ℝ) (hδ : 0 < δ) (a : ℝ) :
    SchwartzMap ℝ ℂ :=
  preSiftedHybridTranslateSchwartz (preSiftedHybridKernelSchwartz δ hδ) a

/--
Definition: the finite Schwartz sum that localizes coefficients at their logarithms.

Input: a finite index set, complex coefficients, and a positive kernel scale.

Output: the sum of translated scaled kernels with the given coefficients.

Role: supplies the smooth finite function to which Plancherel is applied.
-/
noncomputable def preSiftedHybridLocalizedSchwartz (δ : ℝ) (hδ : 0 < δ) (s : Finset ℕ) (c : ℕ → ℂ) :
    SchwartzMap ℝ ℂ :=
  ∑ n ∈ s, c n • preSiftedHybridTranslatedKernelSchwartz δ hδ (Real.log n)

/--
Definition: the finite Dirichlet polynomial with coefficients supported on `s`.

Definition: `Σ n ∈ s, c n * exp(-it log n)`.

Role: the height integral of its squared norm is bounded by the localized Schwartz sum.
-/
noncomputable def preSiftedHybridDirichletPolynomial (s : Finset ℕ) (c : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ s, c n * Complex.exp ((-(t * Real.log n) : ℝ) * Complex.I)

/--
Claim: the Fourier transform of the localized Schwartz sum factors into the kernel transform and
the finite Dirichlet polynomial at frequency `2πξ`.

Proof: apply the finite-sum translation formula, then rewrite each circle phase as its complex
exponential and factor out the common kernel transform.

Role: connects height integration of a finite Dirichlet polynomial to Plancherel.
-/
theorem preSiftedHybridLocalizedSchwartz_fourier (δ : ℝ) (hδ : 0 < δ) (s : Finset ℕ) (c : ℕ → ℂ)
    (ξ : ℝ) :
    (FourierTransform.fourier (preSiftedHybridLocalizedSchwartz δ hδ s c) : ℝ → ℂ) ξ =
      (FourierTransform.fourier (preSiftedHybridKernelSchwartz δ hδ) : ℝ → ℂ) ξ *
        ∑ n ∈ s, c n * Complex.exp ((-2 * Real.pi * Real.log n * ξ) * Complex.I) := by
  simp only [preSiftedHybridLocalizedSchwartz, preSiftedHybridTranslatedKernelSchwartz]
  rw [preSiftedHybridTranslateSchwartz_sum_fourier]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]
  push_cast
  ring_nf

/--
Claim: at frequency `t / (2π)`, the localized Schwartz Fourier transform contains the stated
finite Dirichlet polynomial.

Proof: substitute `ξ = t / (2π)` in the Fourier factorization and cancel the frequency scale in
each exponential.

Role: identifies the Fourier integral used in the height localization estimate.
-/
theorem preSiftedHybridLocalizedSchwartz_fourier_at_height (δ : ℝ) (hδ : 0 < δ) (s : Finset ℕ)
    (c : ℕ → ℂ) (t : ℝ) :
    (FourierTransform.fourier (preSiftedHybridLocalizedSchwartz δ hδ s c) : ℝ → ℂ)
        (t / (2 * Real.pi)) =
      (FourierTransform.fourier (preSiftedHybridKernelSchwartz δ hδ) : ℝ → ℂ) (t / (2 * Real.pi)) *
        preSiftedHybridDirichletPolynomial s c t := by
  rw [preSiftedHybridLocalizedSchwartz_fourier]
  unfold preSiftedHybridDirichletPolynomial
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  congr 1
  have hphase : -2 * Real.pi * Real.log n * (t / (2 * Real.pi)) = -(t * Real.log n) := by
    field_simp [Real.pi_ne_zero]
  convert congrArg (fun r : ℝ => Complex.exp ((r : ℂ) * Complex.I)) hphase using 1; push_cast; ring

/--
Definition: translate the unit-mass window by `a` as the Schwartz function `x ↦ φ(x - a)`.

Role: provides a fixed smooth window centered at each logarithm in a finite Dirichlet polynomial.
-/
noncomputable def preSiftedHybridTranslatedUnitWindowSchwartz (a : ℝ) : SchwartzMap ℝ ℂ :=
  preSiftedHybridTranslateSchwartz preSiftedHybridUnitWindowSchwartz a

/--
Claim: the translated Schwartz window evaluates to the unit window at `x - a`.

Role: exposes the pointwise window used in the finite Dirichlet polynomial localization.
-/
theorem coe_preSiftedHybridTranslatedUnitWindowSchwartz (a : ℝ) :
    (preSiftedHybridTranslatedUnitWindowSchwartz a : ℝ → ℂ) = fun x =>
      preSiftedHybridUnitWindowComplex (x - a) := by
  rw [preSiftedHybridTranslatedUnitWindowSchwartz, coe_preSiftedHybridTranslateSchwartz,
    coe_preSiftedHybridUnitWindowSchwartz]

/--
Claim: translating the unit window multiplies its Fourier transform by the corresponding phase.

Role: gives the Fourier factorization for each term of the localized finite Dirichlet polynomial.
-/
theorem preSiftedHybridTranslatedUnitWindowSchwartz_fourier (a ξ : ℝ) :
    (FourierTransform.fourier (preSiftedHybridTranslatedUnitWindowSchwartz a) : ℝ → ℂ) ξ =
      Real.fourierChar ((-a) * ξ) •
        (FourierTransform.fourier preSiftedHybridUnitWindowSchwartz : ℝ → ℂ) ξ := by
  exact preSiftedHybridTranslateSchwartz_fourier preSiftedHybridUnitWindowSchwartz a ξ

/--
Claim: the scaled Schwartz kernel represents the complexification of the real hybrid kernel.

Proof: evaluate the Schwartz composition, then use linearity of the real-to-complex map.

Role: connects the real kernel mass estimates to its complex Fourier transform.
-/
theorem coe_preSiftedHybridKernelSchwartz (δ : ℝ) (hδ : 0 < δ) :
    (preSiftedHybridKernelSchwartz δ hδ : ℝ → ℂ) = fun x =>
      Complex.ofRealCLM (preSiftedHybridKernel δ x) := by
  funext x
  change
    δ⁻¹ • Complex.ofRealCLM (preSiftedHybridUnitWindow (x * δ⁻¹)) =
      Complex.ofRealCLM (δ⁻¹ * preSiftedHybridUnitWindow (δ⁻¹ * x))
  rw [← Complex.ofRealCLM.map_smul]
  simp only [smul_eq_mul, mul_comm]

/--
Claim: the translated scaled kernel is the complexification of `x ↦ κδ(x - a)`.

Role: connects pointwise finite-sum localization to the real kernel bounds.
-/
theorem coe_preSiftedHybridTranslatedKernelSchwartz (δ : ℝ) (hδ : 0 < δ) (a : ℝ) :
    (preSiftedHybridTranslatedKernelSchwartz δ hδ a : ℝ → ℂ) = fun x =>
      Complex.ofRealCLM (preSiftedHybridKernel δ (x - a)) := by
  rw [preSiftedHybridTranslatedKernelSchwartz, coe_preSiftedHybridTranslateSchwartz,
    coe_preSiftedHybridKernelSchwartz]

/--
Claim: evaluation of the localized Schwartz sum is the finite sum of its translated real kernels.

Proof: evaluate the finite sum termwise and use the translated-kernel coercion formula.

Role: exposes the pointwise coefficient sum used by the local pre-sifted large sieve.
-/
theorem coe_preSiftedHybridLocalizedSchwartz (δ : ℝ) (hδ : 0 < δ) (s : Finset ℕ) (c : ℕ → ℂ) :
    (preSiftedHybridLocalizedSchwartz δ hδ s c : ℝ → ℂ) = fun x =>
      ∑ n ∈ s, c n * (preSiftedHybridKernel δ (x - Real.log n) : ℂ) := by
  funext x
  rw [preSiftedHybridLocalizedSchwartz, coe_sum_smul_preSiftedHybridSchwartz]
  simp only [smul_eq_mul]
  apply Finset.sum_congr rfl
  intro n hn
  congr 1
  simpa only [Complex.ofRealCLM_apply] using
    congrFun (coe_preSiftedHybridTranslatedKernelSchwartz δ hδ (Real.log n)) x

/--
Claim: dilation of the hybrid kernel rescales its Fourier transform by the reciprocal frequency.

Proof: write both Schwartz Fourier transforms as integrals, change variables by the dilation, and
cancel the resulting scalar factors.

Role: transfers the unit-window Fourier lower bound to the scale used in height localization.
-/
theorem preSiftedHybridKernelSchwartz_fourier_eq_unitWindow (δ : ℝ) (hδ : 0 < δ) (ξ : ℝ) :
    (FourierTransform.fourier (preSiftedHybridKernelSchwartz δ hδ) : ℝ → ℂ) ξ =
      (FourierTransform.fourier preSiftedHybridUnitWindowSchwartz : ℝ → ℂ) (δ * ξ) := by
  let f : ℝ → ℂ := fun y =>
    Complex.exp ((-2 * Real.pi * y * (δ * ξ)) * Complex.I) * preSiftedHybridUnitWindowComplex y
  have hchange : ∫ x : ℝ, f (δ⁻¹ * x) = δ • ∫ y : ℝ, f y := by
    have h := MeasureTheory.Measure.integral_comp_mul_left f δ⁻¹
    rw [inv_inv, abs_of_pos hδ] at h
    exact h
  have hscaled :
    (FourierTransform.fourier (preSiftedHybridKernelSchwartz δ hδ) : ℝ → ℂ) ξ =
      ∫ x : ℝ, δ⁻¹ • f (δ⁻¹ * x) := by
    calc
      (FourierTransform.fourier (preSiftedHybridKernelSchwartz δ hδ) : ℝ → ℂ) ξ =
          ∫ x : ℝ,
            Complex.exp (-2 * Real.pi * (x : ℂ) * ξ * Complex.I) *
              (preSiftedHybridKernel δ x : ℂ) :=
        by
        have hf := preSiftedHybrid_fourier_eq_integral_exp (preSiftedHybridKernelSchwartz δ hδ) ξ
        simpa only [coe_preSiftedHybridKernelSchwartz, Complex.ofRealCLM_apply] using hf
      _ = ∫ x : ℝ, δ⁻¹ • f (δ⁻¹ * x) := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [] with x
        have hp :
          Complex.exp ((-2 * Real.pi * x * ξ) * Complex.I) * (preSiftedHybridKernel δ x : ℂ) =
            δ⁻¹ •
              (Complex.exp ((-2 * Real.pi * (δ⁻¹ * x) * (δ * ξ)) * Complex.I) *
                preSiftedHybridUnitWindowComplex (δ⁻¹ * x)) := by
          have hc :
            Complex.ofRealCLM (preSiftedHybridKernel δ x) =
              δ⁻¹ • preSiftedHybridUnitWindowComplex (δ⁻¹ * x) := by
            rw [preSiftedHybridKernel]
            change
              Complex.ofRealCLM (δ⁻¹ * preSiftedHybridUnitWindow (δ⁻¹ * x)) =
                δ⁻¹ • Complex.ofRealCLM (preSiftedHybridUnitWindow (δ⁻¹ * x))
            rw [← Complex.ofRealCLM.map_smul]
            simp only [smul_eq_mul]
          have hcCast :
            (preSiftedHybridKernel δ x : ℂ) = δ⁻¹ • preSiftedHybridUnitWindowComplex (δ⁻¹ * x) := by
            simpa only [Complex.ofRealCLM_apply] using hc
          have ha : -2 * Real.pi * x * ξ = -2 * Real.pi * (δ⁻¹ * x) * (δ * ξ) := by
            calc
              -2 * Real.pi * x * ξ = -2 * Real.pi * (δ⁻¹ * δ) * x * ξ := by
                rw [inv_mul_cancel₀ (ne_of_gt hδ)]
                ring
              _ = -2 * Real.pi * (δ⁻¹ * x) * (δ * ξ) := by ring
          have he :
            Complex.exp ((-2 * Real.pi * x * ξ) * Complex.I) =
              Complex.exp ((-2 * Real.pi * (δ⁻¹ * x) * (δ * ξ)) * Complex.I) := by
            convert congrArg (fun r : ℝ => Complex.exp ((r : ℂ) * Complex.I)) ha using 1 <;>
              push_cast <;>
              ring
          rw [hcCast, Complex.real_smul, Complex.real_smul, he]
          ring
        convert hp using 1
        dsimp [f]
        congr 2
        push_cast
        rfl
  calc
    (FourierTransform.fourier (preSiftedHybridKernelSchwartz δ hδ) : ℝ → ℂ) ξ =
        ∫ x : ℝ, δ⁻¹ • f (δ⁻¹ * x) :=
      hscaled
    _ = δ⁻¹ • ∫ x : ℝ, f (δ⁻¹ * x) := by rw [MeasureTheory.integral_smul]
    _ = δ⁻¹ • (δ • ∫ y : ℝ, f y) := congrArg (fun z : ℂ => δ⁻¹ • z) hchange
    _ = ∫ y : ℝ, f y := by rw [smul_smul, inv_mul_cancel₀ (ne_of_gt hδ), one_smul]
    _ = (FourierTransform.fourier preSiftedHybridUnitWindowSchwartz : ℝ → ℂ) (δ * ξ) := by
      symm
      have hu := preSiftedHybridUnitWindowSchwartz_fourier_eq_integral (δ * ξ)
      convert hu using 1
      dsimp [f]
      push_cast
      rfl

/--
Claim: the scaled hybrid kernel has Fourier transform norm at least `1/2` at small frequencies.

Input: `2 * π * |δ * ξ| ≤ 1/4`.

Proof: apply the Fourier scaling identity and the unit-window lower bound.

Role: supplies the nonvanishing Fourier factor in the height localization argument.
-/
theorem norm_preSiftedHybridKernelSchwartz_fourier_ge_half (δ : ℝ) (hδ : 0 < δ) {ξ : ℝ}
    (hξ : 2 * Real.pi * |δ * ξ| ≤ 1 / 4) :
    1 / 2 ≤ ‖(FourierTransform.fourier (preSiftedHybridKernelSchwartz δ hδ) : ℝ → ℂ) ξ‖ := by
  rw [preSiftedHybridKernelSchwartz_fourier_eq_unitWindow]
  exact norm_preSiftedHybridUnitWindow_fourier_ge_half hξ

/--
Claim: the scaled hybrid kernel has Fourier transform norm at least `1/2` on the indicated
height interval.

Input: `δ > 0` and `δ * |t| ≤ 1/4`.

Proof: convert the height `t` to the Fourier frequency `t / (2π)` and apply the scaled lower bound.

Role: gives the uniform Fourier lower bound needed to recover the height integral from localization.
-/
theorem norm_preSiftedHybridKernelSchwartz_fourier_ge_half_of_height (δ : ℝ) (hδ : 0 < δ) {t : ℝ}
    (ht : δ * |t| ≤ 1 / 4) :
    1 / 2 ≤
      ‖(FourierTransform.fourier (preSiftedHybridKernelSchwartz δ hδ) : ℝ → ℂ)
          (t / (2 * Real.pi))‖ := by
  have hπ : 0 < 2 * Real.pi := by positivity
  have hfreq : 2 * Real.pi * |δ * (t / (2 * Real.pi))| = δ * |t| := by
    rw [abs_mul, abs_div, abs_of_pos hδ, abs_of_pos hπ]
    field_simp
  exact
    norm_preSiftedHybridKernelSchwartz_fourier_ge_half δ hδ
      (by
        rw [hfreq]; exact ht)

/--
Claim: the dilated hybrid kernel is integrable for positive scale.

Proof: compose the integrable unit window with a nonzero dilation, then multiply by the constant
`δ⁻¹`.

Role: justifies its Lebesgue integral and subsequent Plancherel estimates.
-/
theorem preSiftedHybridKernel_integrable (δ : ℝ) (hδ : 0 < δ) :
    MeasureTheory.Integrable (preSiftedHybridKernel δ) MeasureTheory.volume := by
  change
    MeasureTheory.Integrable (fun x : ℝ => δ⁻¹ * preSiftedHybridUnitWindow (δ⁻¹ * x))
      MeasureTheory.volume
  have hcomp :
    MeasureTheory.Integrable (fun x : ℝ => preSiftedHybridUnitWindow (δ⁻¹ * x))
      MeasureTheory.volume :=
    (MeasureTheory.integrable_comp_mul_left_iff preSiftedHybridUnitWindow
          (inv_ne_zero (ne_of_gt hδ))).2
      (ContDiffBump.integrable_normed preSiftedHybridUnitBump)
  exact hcomp.const_mul δ⁻¹

/--
Inputs: a positive kernel scale.

Claim: the square of the scaled kernel is integrable on the real line.

Proof: dominate its squared norm by `δ⁻¹` times the integrable nonnegative kernel, using the
unit-window bound by one.

Role: permits termwise integration of the pointwise localized large-sieve estimate.
-/
theorem preSiftedHybridKernel_sq_integrable (δ : ℝ) (hδ : 0 < δ) :
    MeasureTheory.Integrable (fun x : ℝ => preSiftedHybridKernel δ x ^ 2) MeasureTheory.volume := by
  have hucont : Continuous preSiftedHybridUnitWindow := by
    change Continuous (preSiftedHybridUnitBump.normed MeasureTheory.volume)
    exact
      ContDiff.continuous
        (ContDiffBump.contDiff_normed (μ := MeasureTheory.volume) (n := ⊤) preSiftedHybridUnitBump)
  have hkcont : Continuous (preSiftedHybridKernel δ) := by
    change Continuous (fun x : ℝ => δ⁻¹ * preSiftedHybridUnitWindow (δ⁻¹ * x))
    exact continuous_const.mul (hucont.comp (continuous_const.mul continuous_id))
  have hknonneg : ∀ x, 0 ≤ preSiftedHybridKernel δ x := by
    intro x
    change 0 ≤ δ⁻¹ * preSiftedHybridUnitWindow (δ⁻¹ * x)
    exact mul_nonneg (inv_nonneg.mpr hδ.le) (preSiftedHybridUnitWindow_nonneg _)
  have hkbound : ∀ x, preSiftedHybridKernel δ x ≤ δ⁻¹ := by
    intro x
    change δ⁻¹ * preSiftedHybridUnitWindow (δ⁻¹ * x) ≤ δ⁻¹
    calc
      δ⁻¹ * preSiftedHybridUnitWindow (δ⁻¹ * x) ≤ δ⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left (preSiftedHybridUnitWindow_le_one _) (inv_nonneg.mpr hδ.le)
      _ = δ⁻¹ := mul_one _
  have hkernel := preSiftedHybridKernel_integrable δ hδ
  have hmajor :
    MeasureTheory.Integrable (fun x : ℝ => δ⁻¹ * |preSiftedHybridKernel δ x|)
      MeasureTheory.volume := by
    exact hkernel.norm.const_mul δ⁻¹
  refine hmajor.mono' (hkcont.pow 2).aestronglyMeasurable ?_
  filter_upwards [] with x
  change |preSiftedHybridKernel δ x ^ 2| ≤ δ⁻¹ * |preSiftedHybridKernel δ x|
  rw [abs_of_nonneg (sq_nonneg _), abs_of_nonneg (hknonneg x)]
  calc
    preSiftedHybridKernel δ x ^ 2 = preSiftedHybridKernel δ x * preSiftedHybridKernel δ x := by
      rw [pow_two]
    _ ≤ preSiftedHybridKernel δ x * δ⁻¹ := mul_le_mul_of_nonneg_left (hkbound x) (hknonneg x)
    _ = δ⁻¹ * preSiftedHybridKernel δ x := by ring

/--
Inputs: a positive kernel scale, a complex coefficient, and a translation center.

Claim: the integral of the translated kernel coefficient's squared norm factors into the
coefficient energy and the kernel's squared integral.

Proof: expand the complex norm product and use translation invariance of Lebesgue measure.

Role: supplies the termwise integral needed to integrate the pointwise hybrid large-sieve bound.
-/
theorem integral_norm_sq_mul_preSiftedHybridKernel_translate (δ : ℝ) (a : ℂ) (b : ℝ) :
    (∫ x : ℝ, ‖a * (preSiftedHybridKernel δ (x - b) : ℂ)‖ ^ 2 ∂MeasureTheory.volume) =
      ‖a‖ ^ 2 * ∫ x : ℝ, preSiftedHybridKernel δ x ^ 2 ∂MeasureTheory.volume := by
  have hmp :
    MeasureTheory.MeasurePreserving (fun x : ℝ => x - b) MeasureTheory.volume
      MeasureTheory.volume := by
    simpa only [sub_eq_add_neg] using
      MeasureTheory.measurePreserving_add_right MeasureTheory.volume (-b)
  have hpoint (x : ℝ) :
    ‖a * (preSiftedHybridKernel δ (x - b) : ℂ)‖ ^ 2 =
      ‖a‖ ^ 2 * preSiftedHybridKernel δ (x - b) ^ 2 := by
    rw [norm_mul]
    rw [Complex.norm_real]
    rw [Real.norm_eq_abs]
    rw [mul_pow]
    rw [sq_abs]
  calc
    (∫ x : ℝ, ‖a * (preSiftedHybridKernel δ (x - b) : ℂ)‖ ^ 2 ∂MeasureTheory.volume) =
        ∫ x : ℝ, ‖a‖ ^ 2 * preSiftedHybridKernel δ (x - b) ^ 2 ∂MeasureTheory.volume :=
      by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with x
      exact hpoint x
    _ = ‖a‖ ^ 2 * ∫ x : ℝ, preSiftedHybridKernel δ (x - b) ^ 2 ∂MeasureTheory.volume := by
      rw [MeasureTheory.integral_const_mul]
    _ = ‖a‖ ^ 2 * ∫ x : ℝ, preSiftedHybridKernel δ x ^ 2 ∂MeasureTheory.volume := by
      congr 1
      exact
        hmp.integral_comp (Homeomorph.addRight (-b)).measurableEmbedding
          (fun x : ℝ => preSiftedHybridKernel δ x ^ 2)

/--
Inputs: a positive integer, a localization center, and a positive window radius.

Claim: if the logarithm of the integer lies within the window, the integer lies between the
floors of the corresponding exponential endpoints.

Proof: exponentiate the two strict logarithmic inequalities and use the defining floor bounds.

Role: places each locally supported coefficient in the short interval used by the pre-sifted
large sieve.
-/
theorem preSiftedHybrid_nat_mem_floor_exp_Ico {n : ℕ} (hn : 0 < n) (x δ : ℝ)
    (hwindow : |x - Real.log n| < δ) :
    Nat.floor (Real.exp (x - δ)) ≤ n ∧ n < Nat.floor (Real.exp (x + δ)) + 1 := by
  have hwindow' := abs_lt.mp hwindow
  have hloglo : x - δ < Real.log (n : ℝ) := by linarith only [hwindow'.2]
  have hloghi : Real.log (n : ℝ) < x + δ := by linarith only [hwindow'.1]
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hexplo : Real.exp (x - δ) < (n : ℝ) := by
    rw [← Real.exp_log hnR]
    exact Real.exp_lt_exp.mpr hloglo
  have hexphi : (n : ℝ) < Real.exp (x + δ) := by
    rw [← Real.exp_log hnR]
    exact Real.exp_lt_exp.mpr hloghi
  constructor
  · exact Nat.floor_le_of_le hexplo.le
  · exact Nat.lt_succ_of_le ((Nat.le_floor_iff (Real.exp_nonneg (x + δ))).mpr hexphi.le)

/--
Inputs: a positive logarithmic window radius.

Claim: the natural interval from the lower exponential floor to one past the upper floor has size
at most the real exponential width plus two.

Proof: bound the upper floor by its real argument and use that the lower argument is less than one
past its floor.

Role: controls the rounding loss when applying the interval-supported pre-sifted large sieve.
-/
theorem preSiftedHybrid_floor_exp_window_length_le (x δ : ℝ) (hδ : 0 < δ) :
    ((Nat.floor (Real.exp (x + δ)) + 1 - Nat.floor (Real.exp (x - δ)) : ℕ) : ℝ) ≤
      Real.exp (x + δ) - Real.exp (x - δ) + 2 := by
  let lo := Nat.floor (Real.exp (x - δ))
  let hi := Nat.floor (Real.exp (x + δ)) + 1
  have hlohi : lo ≤ hi := by
    dsimp [lo, hi]
    exact Nat.le_succ_of_le (Nat.floor_mono (Real.exp_le_exp.mpr (by linarith only [hδ])))
  have hcast : ((hi - lo : ℕ) : ℝ) = (hi : ℝ) - (lo : ℝ) := Nat.cast_sub hlohi
  have hupper : (Nat.floor (Real.exp (x + δ)) : ℝ) ≤ Real.exp (x + δ) :=
    Nat.floor_le (Real.exp_nonneg (x + δ))
  have hlower : Real.exp (x - δ) < (Nat.floor (Real.exp (x - δ)) : ℝ) + 1 :=
    Nat.lt_floor_add_one (Real.exp (x - δ))
  change ((hi - lo : ℕ) : ℝ) ≤ _
  rw [hcast]
  dsimp [hi, lo]
  push_cast
  linarith only [hupper, hlower]

/--
Inputs: a positive kernel scale and a logarithmic displacement at least that scale.

Claim: the scaled kernel vanishes outside its compact support interval.

Proof: rescale the displacement to absolute value at least one and apply the unit-window support
lemma.

Role: removes coefficients outside the local logarithmic window before applying the short-interval
large sieve.
-/
theorem preSiftedHybridKernel_eq_zero_of_scale_le_abs (δ x : ℝ) (hδ : 0 < δ) (h : δ ≤ |x|) :
    preSiftedHybridKernel δ x = 0 := by
  unfold preSiftedHybridKernel
  have hinv : 0 < δ⁻¹ := inv_pos.mpr hδ
  have habs : 1 ≤ |δ⁻¹ * x| := by
    rw [abs_mul, abs_of_pos hinv]
    have hm := mul_le_mul_of_nonneg_left h hinv.le
    simpa only [inv_mul_cancel₀ (ne_of_gt hδ)] using hm
  simp only [preSiftedHybridUnitWindow_eq_zero_of_one_le_abs habs, mul_zero]

/--
Inputs: a positive kernel scale and a nonzero value of the scaled kernel.

Claim: the displacement lies strictly inside the logarithmic window.

Proof: the support lemma makes the kernel zero whenever the displacement has absolute value at
least the scale.

Role: converts nonzero localized coefficients into the interval support hypothesis.
-/
theorem preSiftedHybridKernel_ne_zero_implies_abs_lt (δ x : ℝ) (hδ : 0 < δ)
    (hK : preSiftedHybridKernel δ x ≠ 0) : |x| < δ := by
  by_contra h
  exact hK (preSiftedHybridKernel_eq_zero_of_scale_le_abs δ x hδ (le_of_not_gt h))

/--
Inputs: a positive integer whose scaled hybrid kernel is nonzero at a logarithmic displacement.

Claim: the integer belongs to the natural interval between the floors of the exponential window
endpoints.

Proof: nonvanishing places the displacement strictly inside the window, so the logarithmic-window
floor bound applies.

Role: turns the support of each localized coefficient into the interval support required by the
pre-sifted short-interval large sieve.
-/
theorem preSiftedHybrid_nat_mem_floor_exp_Ico_of_kernel_ne_zero {n : ℕ} (hn : 0 < n) (x δ : ℝ)
    (hδ : 0 < δ) (hK : preSiftedHybridKernel δ (x - Real.log n) ≠ 0) :
    Nat.floor (Real.exp (x - δ)) ≤ n ∧ n < Nat.floor (Real.exp (x + δ)) + 1 :=
  preSiftedHybrid_nat_mem_floor_exp_Ico hn x δ
    (preSiftedHybridKernel_ne_zero_implies_abs_lt δ (x - Real.log n) hδ hK)

/--
Inputs: a positive scale no larger than `1/4`.

Claim: the exponential growth across a window of width `2δ` is at most `6δ`.

Proof: apply the rational upper bound for `exp u` on `0 ≤ u < 2`, then simplify using
`δ ≤ 1/4`.

Role: gives a uniform bound for the local interval length in terms of each supported integer.
-/
theorem preSiftedHybrid_exp_two_mul_sub_one_le (δ : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 4) :
    Real.exp (2 * δ) - 1 ≤ 6 * δ := by
  have hu : 0 ≤ 2 * δ := by positivity
  have hu' : 2 * δ < 2 := by linarith only [hδ']
  have hExp := Real.exp_le_two_add_div_two_sub hu hu'
  have hden : 0 < 2 - 2 * δ := by linarith only [hδ']
  have hratio : (2 + 2 * δ) / (2 - 2 * δ) ≤ 1 + 6 * δ := by
    rw [div_le_iff₀ hden]
    have hlin : 0 ≤ 2 - 3 * δ := by linarith only [hδ']
    nlinarith [mul_nonneg hδ.le hlin]
  calc
    Real.exp (2 * δ) - 1 ≤ (2 + 2 * δ) / (2 - 2 * δ) - 1 := sub_le_sub_right hExp 1
    _ ≤ 6 * δ := by linarith only [hratio]

/--
Inputs: a positive integer whose logarithm lies within a positive window of radius at most `1/4`.

Claim: the real exponential interval around the window center has length at most `6δn`.

Proof: factor the interval width as the lower endpoint times `exp (2δ) - 1`, then apply the
exponential increment bound and the lower endpoint estimate from the logarithmic window.

Role: bounds the natural interval length used by the pre-sifted large sieve.
-/
theorem preSiftedHybrid_exp_window_width_le {n : ℕ} (hn : 0 < n) (x δ : ℝ) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 4) (hwindow : |x - Real.log n| < δ) :
    Real.exp (x + δ) - Real.exp (x - δ) ≤ 6 * δ * n := by
  have hwindow' := abs_lt.mp hwindow
  have hlog : x - δ < Real.log (n : ℝ) := by linarith only [hwindow'.2]
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hlo : Real.exp (x - δ) ≤ (n : ℝ) := (Real.exp_lt_exp.mpr hlog).le.trans_eq (Real.exp_log hnR)
  have hfactor := preSiftedHybrid_exp_two_mul_sub_one_le δ hδ hδ'
  have hfactor_nonneg : 0 ≤ Real.exp (2 * δ) - 1 := by
    apply sub_nonneg.mpr
    have hu : 0 ≤ 2 * δ := by positivity
    linarith only [Real.add_one_le_exp (2 * δ), hu]
  have hbase : 0 ≤ Real.exp (x - δ) := (Real.exp_pos _).le
  have hwidth :
    Real.exp (x + δ) - Real.exp (x - δ) = Real.exp (x - δ) * (Real.exp (2 * δ) - 1) := by
    calc
      Real.exp (x + δ) - Real.exp (x - δ) = Real.exp ((x - δ) + 2 * δ) - Real.exp (x - δ) := by
        congr 1
        ring_nf
      _ = Real.exp (x - δ) * Real.exp (2 * δ) - Real.exp (x - δ) := by rw [Real.exp_add]
      _ = _ := by ring
  calc
    Real.exp (x + δ) - Real.exp (x - δ) = Real.exp (x - δ) * (Real.exp (2 * δ) - 1) := hwidth
    _ ≤ Real.exp (x - δ) * (6 * δ) := mul_le_mul_of_nonneg_left hfactor hbase
    _ ≤ (n : ℝ) * (6 * δ) := mul_le_mul_of_nonneg_right hlo (by positivity)
    _ = 6 * δ * n := by ring

/--
Inputs: a rounded interval length, an exponential width bound, and `Z ≥ 1`.

Claim: the pre-sifted large-sieve coefficient is bounded by the local expression
`24δn + 14Z²`.

Proof: absorb the two-unit rounding loss into `8Z²`, then apply the width estimate.

Role: converts the interval-supported large-sieve output into a coefficientwise bound suitable
for integration over the logarithmic axis.
-/
theorem preSiftedHybrid_interval_factor_le (N : ℕ) (W δ n Z : ℝ) (hround : (N : ℝ) ≤ W + 2)
    (hwidth : W ≤ 6 * δ * n) (hZ : 1 ≤ Z) : 4 * (N : ℝ) + 6 * Z ^ 2 ≤ 24 * δ * n + 14 * Z ^ 2 := by
  have hZsq : 1 ≤ Z ^ 2 := by nlinarith [sq_nonneg (Z - 1)]
  nlinarith only [hround, hwidth, hZsq]

/--
Inputs: a modulus greater than one, a finite coefficient support, and a localization kernel.

Claim: restricting to indices where the kernel is nonzero leaves the primitive-character mean
square unchanged.

Proof: each omitted coefficient vanishes by the compact-support lemma, so the finite character
polynomial is unchanged.

Role: lets the short-interval estimate control the original localized finite polynomial.
-/
theorem primitiveCharacterPolynomialMeanSquare_eq_filter_preSiftedHybridKernel {q : ℕ} (hq : 1 < q)
    (s : Finset ℕ) (δ x : ℝ) (a : ℕ → ℂ) :
    primitiveCharacterPolynomialMeanSquare q hq s
        (fun n => a n * (preSiftedHybridKernel δ (x - Real.log (n : ℝ)) : ℂ)) =
      primitiveCharacterPolynomialMeanSquare q hq
        (s.filter fun n : ℕ => preSiftedHybridKernel δ (x - Real.log (n : ℝ)) ≠ 0)
        (fun n => a n * (preSiftedHybridKernel δ (x - Real.log (n : ℝ)) : ℂ)) := by
  classical
  unfold primitiveCharacterPolynomialMeanSquare
  apply Finset.sum_congr rfl
  intro χ hχ
  congr 1
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro n hn hnnot
  have hk : preSiftedHybridKernel δ (x - Real.log (n : ℝ)) = 0 := by
    by_contra hne
    exact hnnot (Finset.mem_filter.mpr ⟨hn, hne⟩)
  simp only [hk, Complex.ofReal_zero, mul_zero, zero_mul]

/--
Inputs: a finite positive support satisfying the pre-sifting condition, a positive scale at most
`1/4`, and a logarithmic center.

Claim: the weighted primitive-character mean square of the kernel-localized coefficients is
bounded by the sum of their squared norms with local weights `24δn + 14Z²`.

Proof: filter to nonzero kernel values, place that support in the rounded exponential interval,
apply the interval-supported pre-sifted large sieve, and bound its factor term by term.

Role: provides the pointwise-in-center large-sieve estimate needed before integrating the
localized Schwartz norm.
-/
theorem preSiftedHybrid_local_mean_square_le (Z : ℕ) (hZ : 2 ≤ Z) (δ : ℝ) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 4) (s : Finset ℕ) (hpos : ∀ n ∈ s, 0 < n)
    (hprime : ∀ n ∈ s, ∀ p, Nat.Prime p → p ∣ n → Z < p) (x : ℝ) (a : ℕ → ℂ) :
    (∑ q ∈ (Finset.Ioc 1 Z).attach,
        Real.log ((Z : ℝ) / (q.val : ℝ)) *
          primitiveCharacterPolynomialMeanSquare q.val
            (show 1 < q.val from (Finset.mem_Ioc.mp q.property).1)
            (s.filter fun n : ℕ => preSiftedHybridKernel δ (x - Real.log (n : ℝ)) ≠ 0)
            (fun n => a n * (preSiftedHybridKernel δ (x - Real.log (n : ℝ)) : ℂ))) ≤
      ∑ n ∈ s,
        ‖a n * (preSiftedHybridKernel δ (x - Real.log (n : ℝ)) : ℂ)‖ ^ 2 *
          (24 * δ * n + 14 * (Z : ℝ) ^ 2) := by
  classical
  let Sx := s.filter fun n : ℕ => preSiftedHybridKernel δ (x - Real.log (n : ℝ)) ≠ 0
  let M := Nat.floor (Real.exp (x - δ))
  let H := Nat.floor (Real.exp (x + δ)) + 1
  let N := H - M
  have hfloor : M ≤ Nat.floor (Real.exp (x + δ)) := by
    dsimp [M]
    apply Nat.floor_mono
    exact Real.exp_le_exp.mpr (by linarith only [hδ])
  have hMH : M ≤ H := by
    dsimp [H]
    exact hfloor.trans (Nat.le_succ _)
  have hMN : M + N = H := by
    dsimp [N]
    exact Nat.add_sub_of_le hMH
  have hSx : Sx ⊆ Finset.Ico M (M + N) := by
    intro n hn
    have hnS : n ∈ s := (Finset.mem_filter.mp hn).1
    have hk : preSiftedHybridKernel δ (x - Real.log (n : ℝ)) ≠ 0 := (Finset.mem_filter.mp hn).2
    have hwindow := preSiftedHybridKernel_ne_zero_implies_abs_lt δ (x - Real.log (n : ℝ)) hδ hk
    have hplace := preSiftedHybrid_nat_mem_floor_exp_Ico (hpos n hnS) x δ hwindow
    rw [Finset.mem_Ico]
    constructor
    · simpa only [M] using hplace.1
    · rw [hMN]
      exact hplace.2
  have hprimeSx : ∀ n ∈ Sx, ∀ p, Nat.Prime p → p ∣ n → Z < p := by
    intro n hn p hp hpn
    exact hprime n (Finset.mem_filter.mp hn).1 p hp hpn
  have hround : (N : ℝ) ≤ Real.exp (x + δ) - Real.exp (x - δ) + 2 := by
    simpa only [N, H, M] using preSiftedHybrid_floor_exp_window_length_le x δ hδ
  have hlarge :=
    primitiveCharacterFamilyMeanSquare_preSifted_le_of_support_Ico Z hZ M N Sx hSx
      (fun n => a n * (preSiftedHybridKernel δ (x - Real.log n) : ℂ)) hprimeSx
  calc
    _ ≤
        (4 * (N : ℝ) + 6 * (Z : ℝ) ^ 2) *
          ∑ n ∈ Sx, ‖a n * (preSiftedHybridKernel δ (x - Real.log (n : ℝ)) : ℂ)‖ ^ 2 :=
      hlarge
    _ =
        ∑ n ∈ Sx,
          ‖a n * (preSiftedHybridKernel δ (x - Real.log (n : ℝ)) : ℂ)‖ ^ 2 *
            (4 * (N : ℝ) + 6 * (Z : ℝ) ^ 2) :=
      by rw [mul_comm, Finset.sum_mul]
    _ ≤
        ∑ n ∈ Sx,
          ‖a n * (preSiftedHybridKernel δ (x - Real.log (n : ℝ)) : ℂ)‖ ^ 2 *
            (24 * δ * n + 14 * (Z : ℝ) ^ 2) :=
      by
      apply Finset.sum_le_sum
      intro n hn
      have hnS : n ∈ s := (Finset.mem_filter.mp hn).1
      have hwindow :=
        preSiftedHybridKernel_ne_zero_implies_abs_lt δ (x - Real.log (n : ℝ)) hδ
          (Finset.mem_filter.mp hn).2
      have hwidth := preSiftedHybrid_exp_window_width_le (hpos n hnS) x δ hδ hδ' hwindow
      have hfactor :=
        preSiftedHybrid_interval_factor_le N (Real.exp (x + δ) - Real.exp (x - δ)) δ n Z hround
          hwidth (by exact_mod_cast (show 1 ≤ Z by omega))
      exact mul_le_mul_of_nonneg_left hfactor (sq_nonneg _)
    _ ≤
        ∑ n ∈ s,
          ‖a n * (preSiftedHybridKernel δ (x - Real.log (n : ℝ)) : ℂ)‖ ^ 2 *
            (24 * δ * n + 14 * (Z : ℝ) ^ 2) :=
      by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro n hn hnot
      positivity

/--
Inputs: the hypotheses of `preSiftedHybrid_local_mean_square_le`.

Claim: the same local estimate holds for coefficients on the original support, with the kernel
making every omitted term vanish.

Proof: rewrite each primitive-character mean square using the kernel-filter invariance lemma.

Role: states the pointwise estimate directly for the finite localized Dirichlet polynomial.
-/
theorem preSiftedHybrid_localized_mean_square_le (Z : ℕ) (hZ : 2 ≤ Z) (δ : ℝ) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 4) (s : Finset ℕ) (hpos : ∀ n ∈ s, 0 < n)
    (hprime : ∀ n ∈ s, ∀ p, Nat.Prime p → p ∣ n → Z < p) (x : ℝ) (a : ℕ → ℂ) :
    (∑ q ∈ (Finset.Ioc 1 Z).attach,
        Real.log ((Z : ℝ) / (q.val : ℝ)) *
          primitiveCharacterPolynomialMeanSquare q.val
            (show 1 < q.val from (Finset.mem_Ioc.mp q.property).1) s
            (fun n => a n * (preSiftedHybridKernel δ (x - Real.log (n : ℝ)) : ℂ))) ≤
      ∑ n ∈ s,
        ‖a n * (preSiftedHybridKernel δ (x - Real.log (n : ℝ)) : ℂ)‖ ^ 2 *
          (24 * δ * n + 14 * (Z : ℝ) ^ 2) := by
  calc
    _ =
        ∑ q ∈ (Finset.Ioc 1 Z).attach,
          Real.log ((Z : ℝ) / (q.val : ℝ)) *
            primitiveCharacterPolynomialMeanSquare q.val
              (show 1 < q.val from (Finset.mem_Ioc.mp q.property).1)
              (s.filter fun n : ℕ => preSiftedHybridKernel δ (x - Real.log (n : ℝ)) ≠ 0)
              (fun n => a n * (preSiftedHybridKernel δ (x - Real.log (n : ℝ)) : ℂ)) :=
      by
      apply Finset.sum_congr rfl
      intro q hq
      congr 1
      exact
        primitiveCharacterPolynomialMeanSquare_eq_filter_preSiftedHybridKernel
          (show 1 < q.val from (Finset.mem_Ioc.mp q.property).1) s δ x a
    _ ≤ _ := preSiftedHybrid_local_mean_square_le Z hZ δ hδ hδ' s hpos hprime x a

/--
Inputs: a positive kernel scale, a finite coefficient support, and a logarithmic center.

Claim: the localized primitive-character mean square is the sum of squared values of the
corresponding localized Schwartz functions.

Proof: expand the primitive-character mean square, express the Schwartz map pointwise as its
finite kernel sum, and reorder each coefficient-character-kernel product.

Role: identifies the pointwise right side of the local sieve estimate with the Schwartz norms
whose integrals are controlled by Plancherel.
-/
theorem primitiveCharacterPolynomialMeanSquare_eq_localizedSchwartz_norm_sq {q : ℕ} (hq : 1 < q)
    (s : Finset ℕ) (δ : ℝ) (hδ : 0 < δ) (x : ℝ) (a : ℕ → ℂ) :
    primitiveCharacterPolynomialMeanSquare q hq s
        (fun n => a n * (preSiftedHybridKernel δ (x - Real.log (n : ℝ)) : ℂ)) =
      ∑ χ ∈ primitiveDirichletCharacterSet q,
        ‖preSiftedHybridLocalizedSchwartz δ hδ s (fun n => a n * χ (n : ZMod q)) x‖ ^ 2 := by
  classical
  unfold primitiveCharacterPolynomialMeanSquare
  apply Finset.sum_congr rfl
  intro χ hχ
  rw [Complex.normSq_eq_norm_sq]
  apply congrArg (fun z : ℂ => ‖z‖ ^ 2)
  rw [coe_preSiftedHybridLocalizedSchwartz]
  apply Finset.sum_congr rfl
  intro n hn
  ring_nf

/--
Claim: every positive dilation of the hybrid kernel has total mass one.

Proof: change variables by `x ↦ δ⁻¹ x` in the Lebesgue integral and use the unit-window mass.

Role: preserves the finite Dirichlet polynomial after convolution with the kernel.
-/
theorem integral_preSiftedHybridKernel (δ : ℝ) (hδ : 0 < δ) :
    ∫ x : ℝ, preSiftedHybridKernel δ x ∂MeasureTheory.volume = 1 := by
  change ∫ x : ℝ, δ⁻¹ * preSiftedHybridUnitWindow (δ⁻¹ * x) ∂MeasureTheory.volume = 1
  rw [MeasureTheory.integral_const_mul]
  rw [MeasureTheory.Measure.integral_comp_mul_left]
  rw [inv_inv, abs_of_pos hδ, integral_preSiftedHybridUnitWindow]
  simp only [smul_eq_mul, mul_one, inv_mul_cancel₀ (ne_of_gt hδ)]

/--
Claim: the squared integral of the positive-scale hybrid kernel is at most `δ⁻¹`.

Proof: change variables in the squared integral and apply the unit window's squared-mass bound.

Role: supplies the scale-dependent factor in the pointwise short-interval estimate.
-/
theorem integral_sq_preSiftedHybridKernel_le (δ : ℝ) (hδ : 0 < δ) :
    ∫ x : ℝ, preSiftedHybridKernel δ x ^ 2 ∂MeasureTheory.volume ≤ δ⁻¹ := by
  change ∫ x : ℝ, (δ⁻¹ * preSiftedHybridUnitWindow (δ⁻¹ * x)) ^ 2 ∂MeasureTheory.volume ≤ δ⁻¹
  have hfun :
    (fun x : ℝ => (δ⁻¹ * preSiftedHybridUnitWindow (δ⁻¹ * x)) ^ 2) = fun x =>
      δ⁻¹ ^ 2 * preSiftedHybridUnitWindow (δ⁻¹ * x) ^ 2 := by
    funext x
    rw [mul_pow]
  have hscale :
    ∫ x : ℝ, preSiftedHybridUnitWindow (δ⁻¹ * x) ^ 2 ∂MeasureTheory.volume =
      δ * ∫ y : ℝ, preSiftedHybridUnitWindow y ^ 2 ∂MeasureTheory.volume := by
    have h :=
      MeasureTheory.Measure.integral_comp_mul_left (fun y : ℝ => preSiftedHybridUnitWindow y ^ 2)
        δ⁻¹
    rw [inv_inv, abs_of_pos hδ] at h
    simpa only [smul_eq_mul] using h
  calc
    ∫ x : ℝ, (δ⁻¹ * preSiftedHybridUnitWindow (δ⁻¹ * x)) ^ 2 ∂MeasureTheory.volume =
        δ⁻¹ ^ 2 * ∫ x : ℝ, preSiftedHybridUnitWindow (δ⁻¹ * x) ^ 2 ∂MeasureTheory.volume :=
      by rw [hfun, MeasureTheory.integral_const_mul]
    _ = δ⁻¹ ^ 2 * (δ * ∫ y : ℝ, preSiftedHybridUnitWindow y ^ 2 ∂MeasureTheory.volume) :=
      congrArg (fun r : ℝ => δ⁻¹ ^ 2 * r) hscale
    _ ≤ δ⁻¹ ^ 2 * (δ * 1) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left integral_sq_preSiftedHybridUnitWindow_le_one (le_of_lt hδ))
        (sq_nonneg _)
    _ = δ⁻¹ := by
      calc
        δ⁻¹ ^ 2 * (δ * 1) = δ⁻¹ * (δ⁻¹ * δ) := by
          rw [pow_two]; ring
        _ = δ⁻¹ := by rw [inv_mul_cancel₀ (ne_of_gt hδ), mul_one]

/--
Inputs: a positive scale, a complex coefficient, and a real translation center.

Claim: the squared norm integral of a translated coefficient times the kernel is at most the
coefficient energy divided by the scale.

Proof: use translation invariance to remove the center, then apply the unit-window square-mass
bound after dilation.

Role: bounds each coefficient's contribution when integrating the local sieve estimate.
-/
theorem integral_norm_sq_mul_preSiftedHybridKernel_translate_le (δ : ℝ) (hδ : 0 < δ) (a : ℂ)
    (b : ℝ) :
    (∫ x : ℝ, ‖a * (preSiftedHybridKernel δ (x - b) : ℂ)‖ ^ 2 ∂MeasureTheory.volume) ≤
      ‖a‖ ^ 2 * δ⁻¹ := by
  rw [integral_norm_sq_mul_preSiftedHybridKernel_translate]
  exact mul_le_mul_of_nonneg_left (integral_sq_preSiftedHybridKernel_le δ hδ) (sq_nonneg ‖a‖)

/--
Inputs: a positive scale, a complex coefficient, and a real translation center.

Claim: the squared norm of the translated coefficient-kernel product is integrable.

Proof: rewrite it as a constant multiple of a translated square-integrable kernel and use
translation invariance of Lebesgue measure.

Role: gives the integrability hypothesis needed to integrate the local coefficient sum.
-/
theorem integrable_norm_sq_mul_preSiftedHybridKernel_translate (δ : ℝ) (hδ : 0 < δ) (a : ℂ)
    (b : ℝ) :
    MeasureTheory.Integrable (fun x : ℝ => ‖a * (preSiftedHybridKernel δ (x - b) : ℂ)‖ ^ 2)
      MeasureTheory.volume := by
  have hmp :
    MeasureTheory.MeasurePreserving (fun x : ℝ => x - b) MeasureTheory.volume
      MeasureTheory.volume := by
    simpa only [sub_eq_add_neg] using
      MeasureTheory.measurePreserving_add_right MeasureTheory.volume (-b)
  have hshift :
    MeasureTheory.Integrable (fun x : ℝ => preSiftedHybridKernel δ (x - b) ^ 2)
      MeasureTheory.volume :=
    hmp.integrable_comp_of_integrable (preSiftedHybridKernel_sq_integrable δ hδ)
  have hpoint (x : ℝ) :
    ‖a * (preSiftedHybridKernel δ (x - b) : ℂ)‖ ^ 2 =
      ‖a‖ ^ 2 * preSiftedHybridKernel δ (x - b) ^ 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  apply (hshift.const_mul (‖a‖ ^ 2)).congr
  exact Filter.Eventually.of_forall fun x => (hpoint x).symm

/--
Inputs: a positive scale, an integer cutoff, a finite coefficient support, and coefficients.

Claim: the coefficient sum on the right side of the pointwise local sieve estimate is integrable.

Proof: each translated coefficient-kernel square is integrable, multiplication by its constant
weight preserves integrability, and the support is finite.

Role: allows integration of the pointwise right side term by term.
-/
theorem integrable_preSiftedHybrid_localized_coefficient_bound (Z : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (s : Finset ℕ) (a : ℕ → ℂ) :
    MeasureTheory.Integrable
      (fun x : ℝ =>
        ∑ n ∈ s,
          ‖a n * (preSiftedHybridKernel δ (x - Real.log n) : ℂ)‖ ^ 2 *
            (24 * δ * n + 14 * (Z : ℝ) ^ 2))
      MeasureTheory.volume := by
  apply MeasureTheory.integrable_finsetSum
  intro n hn
  exact
    (integrable_norm_sq_mul_preSiftedHybridKernel_translate δ hδ (a n) (Real.log n)).mul_const
      (24 * δ * n + 14 * (Z : ℝ) ^ 2)

/--
Inputs: a positive scale, an integer cutoff, a finite coefficient support, and coefficients.

Claim: the integral of the pointwise coefficient bound is at most the energy with weight
`24*n + 14*Z^2/δ`.

Proof: exchange the finite sum and integral, apply the translated-kernel integral bound termwise,
and simplify the resulting scale factors.

Role: produces the integrated right side required for the hybrid estimate.
-/
theorem integral_preSiftedHybrid_localized_coefficient_bound_le (Z : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (s : Finset ℕ) (a : ℕ → ℂ) :
    (∫ x : ℝ,
        ∑ n ∈ s,
          ‖a n * (preSiftedHybridKernel δ (x - Real.log n) : ℂ)‖ ^ 2 *
            (24 * δ * n + 14 * (Z : ℝ) ^ 2) ∂MeasureTheory.volume) ≤
      ∑ n ∈ s, ‖a n‖ ^ 2 * ((24 : ℝ) * n + 14 * (Z : ℝ) ^ 2 / δ) := by
  rw [MeasureTheory.integral_finsetSum _
      (fun n hn =>
        (integrable_norm_sq_mul_preSiftedHybridKernel_translate δ hδ (a n) (Real.log n)).mul_const
          (24 * δ * n + 14 * (Z : ℝ) ^ 2))]
  simp_rw [MeasureTheory.integral_mul_const]
  calc
    (∑ n ∈ s,
          (∫ x : ℝ,
              ‖a n * (preSiftedHybridKernel δ (x - Real.log n) : ℂ)‖ ^ 2 ∂MeasureTheory.volume) *
            (24 * δ * n + 14 * (Z : ℝ) ^ 2)) ≤
        ∑ n ∈ s, (‖a n‖ ^ 2 * δ⁻¹) * (24 * δ * n + 14 * (Z : ℝ) ^ 2) :=
      by
      apply Finset.sum_le_sum
      intro n hn
      exact
        mul_le_mul_of_nonneg_right
          (integral_norm_sq_mul_preSiftedHybridKernel_translate_le δ hδ (a n) (Real.log n))
          (by positivity)
    _ = ∑ n ∈ s, ‖a n‖ ^ 2 * ((24 : ℝ) * n + 14 * (Z : ℝ) ^ 2 / δ) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [div_eq_mul_inv]
      have hscale : δ⁻¹ * (24 * δ * (n : ℝ)) = 24 * n := by
        calc
          δ⁻¹ * (24 * δ * (n : ℝ)) = 24 * (δ⁻¹ * δ) * n := by ring
          _ = 24 * n := by rw [inv_mul_cancel₀ (ne_of_gt hδ), mul_one]
      calc
        ‖a n‖ ^ 2 * δ⁻¹ * (24 * δ * n + 14 * (Z : ℝ) ^ 2) =
            ‖a n‖ ^ 2 * δ⁻¹ * (24 * δ * n) + ‖a n‖ ^ 2 * δ⁻¹ * (14 * (Z : ℝ) ^ 2) :=
          by rw [mul_add]
        _ = ‖a n‖ ^ 2 * (δ⁻¹ * (24 * δ * n)) + ‖a n‖ ^ 2 * (14 * (Z : ℝ) ^ 2 * δ⁻¹) := by ring
        _ = ‖a n‖ ^ 2 * (24 * n) + ‖a n‖ ^ 2 * (14 * (Z : ℝ) ^ 2 * δ⁻¹) := by rw [hscale]
        _ = ‖a n‖ ^ 2 * (24 * n + 14 * (Z : ℝ) ^ 2 * δ⁻¹) := by ring

/--
Claim: inside the height range selected by the kernel scale, the Dirichlet polynomial is
pointwise bounded by four times the squared Fourier transform of its localized Schwartz sum.

Proof: use the lower bound for the kernel transform in the finite-sum Fourier factorization.

Role: supplies the pointwise input for integration over a bounded height interval.
-/
theorem preSiftedHybridLocalizedSchwartz_pointwise_le_fourier_sq (δ : ℝ) (hδ : 0 < δ) (s : Finset ℕ)
    (c : ℕ → ℂ) (t : ℝ) (ht : δ * |t| ≤ 1 / 4) :
    ‖preSiftedHybridDirichletPolynomial s c t‖ ^ 2 ≤
      4 *
        ‖(FourierTransform.fourier (preSiftedHybridLocalizedSchwartz δ hδ s c) : ℝ → ℂ)
              (t / (2 * Real.pi))‖ ^
          2 := by
  have hk := norm_preSiftedHybridKernelSchwartz_fourier_ge_half_of_height δ hδ ht
  have hfactor := preSiftedHybridLocalizedSchwartz_fourier_at_height δ hδ s c t
  have hnorm :
    ‖(FourierTransform.fourier (preSiftedHybridLocalizedSchwartz δ hδ s c) : ℝ → ℂ)
          (t / (2 * Real.pi))‖ =
      ‖(FourierTransform.fourier (preSiftedHybridKernelSchwartz δ hδ) : ℝ → ℂ)
            (t / (2 * Real.pi))‖ *
        ‖preSiftedHybridDirichletPolynomial s c t‖ := by
    rw [hfactor, norm_mul]
  have hmul :=
    mul_le_mul_of_nonneg_right hk (norm_nonneg (preSiftedHybridDirichletPolynomial s c t))
  have hle :
    ‖preSiftedHybridDirichletPolynomial s c t‖ ≤
      2 *
        (‖(FourierTransform.fourier (preSiftedHybridKernelSchwartz δ hδ) : ℝ → ℂ)
              (t / (2 * Real.pi))‖ *
          ‖preSiftedHybridDirichletPolynomial s c t‖) := by
    nlinarith [hmul]
  rw [hnorm]
  calc
    ‖preSiftedHybridDirichletPolynomial s c t‖ ^ 2 ≤
        (2 *
            (‖(FourierTransform.fourier (preSiftedHybridKernelSchwartz δ hδ) : ℝ → ℂ)
                  (t / (2 * Real.pi))‖ *
              ‖preSiftedHybridDirichletPolynomial s c t‖)) ^
          2 :=
      (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hle
    _ =
        4 *
          (‖(FourierTransform.fourier (preSiftedHybridKernelSchwartz δ hδ) : ℝ → ℂ)
                  (t / (2 * Real.pi))‖ *
              ‖preSiftedHybridDirichletPolynomial s c t‖) ^
            2 :=
      by ring

/--
Inputs: a positive window scale, a height cutoff, and a finite Dirichlet polynomial.

Claim: when the scaled height interval lies in the Fourier nonvanishing range, its squared
integral is at most four times the corresponding integral of the localized Schwartz transform.

Proof: integrate the pointwise Fourier lower bound over the interval.

Role: supplies the first integral step toward the height localization estimate.
-/
theorem preSiftedHybridDirichletPolynomial_intervalIntegral_le_fourier (δ T : ℝ) (hδ : 0 < δ)
    (hT : 0 ≤ T) (hδT : δ * T ≤ 1 / 4) (s : Finset ℕ) (c : ℕ → ℂ) :
    (∫ t in (-T)..T, ‖preSiftedHybridDirichletPolynomial s c t‖ ^ 2) ≤
      4 *
        (∫ t in (-T)..T,
          ‖(FourierTransform.fourier (preSiftedHybridLocalizedSchwartz δ hδ s c) : ℝ → ℂ)
                (t / (2 * Real.pi))‖ ^
            2) := by
  have hcontP : Continuous (fun t : ℝ => preSiftedHybridDirichletPolynomial s c t) := by
    unfold preSiftedHybridDirichletPolynomial
    apply continuous_finsetSum
    intro n hn
    apply Continuous.mul continuous_const
    have harg : Continuous (fun t : ℝ => -(t * Real.log n)) :=
      (continuous_id.mul continuous_const).neg
    exact Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp harg).mul continuous_const)
  have hcontF :
    Continuous
      (fun t : ℝ =>
        (FourierTransform.fourier (preSiftedHybridLocalizedSchwartz δ hδ s c) : ℝ → ℂ)
          (t / (2 * Real.pi))) :=
    (SchwartzMap.continuous
          (FourierTransform.fourier (preSiftedHybridLocalizedSchwartz δ hδ s c))).comp
      (continuous_id.div_const (2 * Real.pi))
  have hPint :
    IntervalIntegrable (fun t : ℝ => ‖preSiftedHybridDirichletPolynomial s c t‖ ^ 2)
      MeasureTheory.volume (-T) T :=
    (hcontP.norm.pow 2).intervalIntegrable _ _
  have hFcont :
    Continuous
      (fun t : ℝ =>
        4 *
          ‖(FourierTransform.fourier (preSiftedHybridLocalizedSchwartz δ hδ s c) : ℝ → ℂ)
                (t / (2 * Real.pi))‖ ^
            2) :=
    continuous_const.mul (hcontF.norm.pow 2)
  have hFint :
    IntervalIntegrable
      (fun t : ℝ =>
        4 *
          ‖(FourierTransform.fourier (preSiftedHybridLocalizedSchwartz δ hδ s c) : ℝ → ℂ)
                (t / (2 * Real.pi))‖ ^
            2)
      MeasureTheory.volume (-T) T :=
    hFcont.intervalIntegrable _ _
  have hab : -T ≤ T := by linarith only [hT]
  calc
    _ ≤
        ∫ t in (-T)..T,
          4 *
            ‖(FourierTransform.fourier (preSiftedHybridLocalizedSchwartz δ hδ s c) : ℝ → ℂ)
                  (t / (2 * Real.pi))‖ ^
              2 :=
      by
      apply intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hab hPint hFint
      intro t ht
      have habs : |t| ≤ T := abs_le.mpr ⟨by linarith only [ht.1], ht.2⟩
      have hscale : δ * |t| ≤ 1 / 4 := (mul_le_mul_of_nonneg_left habs hδ.le).trans hδT
      exact preSiftedHybridLocalizedSchwartz_pointwise_le_fourier_sq δ hδ s c t hscale
    _ =
        4 *
          (∫ t in (-T)..T,
            ‖(FourierTransform.fourier (preSiftedHybridLocalizedSchwartz δ hδ s c) : ℝ → ℂ)
                  (t / (2 * Real.pi))‖ ^
              2) :=
      by rw [intervalIntegral.integral_const_mul]

/--
Claim: the Fourier-transform integral in height coordinates equals `2π` times its integral in
Fourier-frequency coordinates.

Proof: apply the interval change of variables `t = 2πξ`.

Role: prepares the localized integral for the Schwartz–Plancherel identity.
-/
theorem preSiftedHybridFourier_intervalIntegral_eq_frequency (T : ℝ) (F : SchwartzMap ℝ ℂ) :
    (∫ t in (-T)..T, ‖(FourierTransform.fourier F : ℝ → ℂ) (t / (2 * Real.pi))‖ ^ 2) =
      2 * Real.pi *
        (∫ ξ in (-(T / (2 * Real.pi)))..(T / (2 * Real.pi)),
          ‖(FourierTransform.fourier F : ℝ → ℂ) ξ‖ ^ 2) := by
  change
    (∫ t in (-T)..T,
        (fun ξ : ℝ => ‖(FourierTransform.fourier F : ℝ → ℂ) ξ‖ ^ 2) (t / (2 * Real.pi))) =
      _
  rw [intervalIntegral.integral_comp_div (f := fun ξ : ℝ =>
      ‖(FourierTransform.fourier F : ℝ → ℂ) ξ‖ ^ 2) (by positivity)]
  simp only [smul_eq_mul, neg_div]

/--
Claim: the squared norm of a Schwartz function is integrable over the real line.

Proof: bound the Schwartz function uniformly by its zeroth seminorm and dominate its squared
norm by a constant multiple of its integrable norm.

Role: justifies enlarging a finite Fourier-frequency interval to the full Plancherel integral.
-/
theorem integrable_norm_sq_of_schwartz (F : SchwartzMap ℝ ℂ) :
    MeasureTheory.Integrable (fun x : ℝ => ‖F x‖ ^ 2) MeasureTheory.volume := by
  let C : ℝ := max 1 (SchwartzMap.seminorm ℂ 0 0 F)
  have hbound : ∀ x : ℝ, ‖F x‖ ≤ C := by
    intro x
    have h := SchwartzMap.le_seminorm ℂ 0 0 F x
    have h' : ‖F x‖ ≤ SchwartzMap.seminorm ℂ 0 0 F := by
      simpa only [pow_zero, one_mul, norm_iteratedFDeriv_zero] using h
    exact h'.trans (le_max_right _ _)
  have hF : MeasureTheory.Integrable F MeasureTheory.volume := F.integrable
  have hmajor : MeasureTheory.Integrable (fun x : ℝ => C * ‖F x‖) MeasureTheory.volume := by
    simpa only [mul_comm] using hF.norm.const_mul C
  have hcont : Continuous (fun x : ℝ => ‖F x‖ ^ 2) := (SchwartzMap.continuous F).norm.pow 2
  refine hmajor.mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖F x‖)]
  rw [pow_two]
  calc
    ‖F x‖ * ‖F x‖ = ‖F x‖ ^ 1 * ‖F x‖ := by simp only [pow_one]
    _ ≤ C * ‖F x‖ :=
      mul_le_mul_of_nonneg_right (by simpa only [pow_one] using hbound x) (norm_nonneg (F x))

/--
Inputs: a modulus, a finite coefficient support, a positive kernel scale, and coefficients.

Claim: the localized primitive-character mean square is integrable on the logarithmic axis.

Proof: rewrite it as the finite sum of squared norms of the localized Schwartz maps, then use
integrability of each Schwartz norm square and closure under finite sums.

Role: justifies integrating the pointwise pre-sifted large-sieve inequality.
-/
theorem integrable_primitiveCharacterPolynomialMeanSquare_localized {q : ℕ} (hq : 1 < q)
    (s : Finset ℕ) (δ : ℝ) (hδ : 0 < δ) (a : ℕ → ℂ) :
    MeasureTheory.Integrable
      (fun x : ℝ =>
        primitiveCharacterPolynomialMeanSquare q hq s
          (fun n => a n * (preSiftedHybridKernel δ (x - Real.log n) : ℂ)))
      MeasureTheory.volume := by
  have hpoint :
    (fun x : ℝ =>
        primitiveCharacterPolynomialMeanSquare q hq s
          (fun n => a n * (preSiftedHybridKernel δ (x - Real.log n) : ℂ))) =
      fun x =>
      ∑ χ ∈ primitiveDirichletCharacterSet q,
        ‖preSiftedHybridLocalizedSchwartz δ hδ s (fun n => a n * χ (n : ZMod q)) x‖ ^ 2 := by
    funext x
    exact primitiveCharacterPolynomialMeanSquare_eq_localizedSchwartz_norm_sq hq s δ hδ x a
  rw [hpoint]
  apply MeasureTheory.integrable_finsetSum
  intro χ hχ
  exact
    integrable_norm_sq_of_schwartz
      (preSiftedHybridLocalizedSchwartz δ hδ s (fun n => a n * χ (n : ZMod q)))

/--
Inputs: a finite modulus range, a finite coefficient support, a positive kernel scale, and
coefficients.

Claim: the log-weighted family of localized primitive-character mean squares is integrable.

Proof: each fixed-modulus mean square is integrable, and the attached modulus sum is finite.

Role: supplies integrability for exchanging the modulus and height integrals in the hybrid bound.
-/
theorem integrable_preSiftedHybrid_localized_family (Z : ℕ) (s : Finset ℕ) (δ : ℝ) (hδ : 0 < δ)
    (a : ℕ → ℂ) :
    MeasureTheory.Integrable
      (fun x : ℝ =>
        ∑ q ∈ (Finset.Ioc 1 Z).attach,
          Real.log ((Z : ℝ) / (q.val : ℝ)) *
            primitiveCharacterPolynomialMeanSquare q.val
              (show 1 < q.val from (Finset.mem_Ioc.mp q.property).1) s
              (fun n => a n * (preSiftedHybridKernel δ (x - Real.log n) : ℂ)))
      MeasureTheory.volume := by
  apply MeasureTheory.integrable_finsetSum
  intro q hq
  exact
    (integrable_primitiveCharacterPolynomialMeanSquare_localized
          (show 1 < q.val from (Finset.mem_Ioc.mp q.property).1) s δ hδ a).const_mul
      (Real.log ((Z : ℝ) / (q.val : ℝ)))

/--
Inputs: a finite modulus cutoff, a finite coefficient support, and a positive kernel scale.

Claim: integrating the localized family mean square equals the finite sum of its modulus-wise
integrals with the logarithmic weights outside.

Proof: apply the finite-sum integral interchange using the integrability established above, then
move each real constant weight outside its integral.

Role: separates the finite modulus sum before applying the height localization estimate.
-/
theorem integral_preSiftedHybrid_localized_family_eq (Z : ℕ) (s : Finset ℕ) (δ : ℝ) (hδ : 0 < δ)
    (a : ℕ → ℂ) :
    (∫ x : ℝ,
        ∑ q ∈ (Finset.Ioc 1 Z).attach,
          Real.log ((Z : ℝ) / (q.val : ℝ)) *
            primitiveCharacterPolynomialMeanSquare q.val
              (show 1 < q.val from (Finset.mem_Ioc.mp q.property).1) s
              (fun n =>
                a n * (preSiftedHybridKernel δ (x - Real.log n) : ℂ)) ∂MeasureTheory.volume) =
      ∑ q ∈ (Finset.Ioc 1 Z).attach,
        Real.log ((Z : ℝ) / (q.val : ℝ)) *
          ∫ x : ℝ,
            primitiveCharacterPolynomialMeanSquare q.val
              (show 1 < q.val from (Finset.mem_Ioc.mp q.property).1) s
              (fun n =>
                a n * (preSiftedHybridKernel δ (x - Real.log n) : ℂ)) ∂MeasureTheory.volume := by
  rw [MeasureTheory.integral_finsetSum _
      (fun q hq =>
        (integrable_primitiveCharacterPolynomialMeanSquare_localized
              (show 1 < q.val from (Finset.mem_Ioc.mp q.property).1) s δ hδ a).const_mul
          (Real.log ((Z : ℝ) / (q.val : ℝ))))]
  simp only [MeasureTheory.integral_const_mul]

/--
Inputs: a pre-sifting cutoff, a positive kernel scale at most `1/4`, and finite supported
coefficients satisfying the pre-sifting condition.

Claim: the integral of the localized weighted primitive-character mean square is bounded by the
coefficient energy with weight `24n + 14Z²/δ`.

Proof: integrate the pointwise local sieve estimate, using integrability of both finite sums, and
apply the termwise translated-kernel square-integral bound.

Role: connects the short-interval sieve estimate to the height-integrated hybrid estimate.
-/
theorem integral_preSiftedHybrid_localized_family_le (Z : ℕ) (hZ : 2 ≤ Z) (δ : ℝ) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 4) (s : Finset ℕ) (hpos : ∀ n ∈ s, 0 < n)
    (hprime : ∀ n ∈ s, ∀ p, Nat.Prime p → p ∣ n → Z < p) (a : ℕ → ℂ) :
    (∫ x : ℝ,
        ∑ q ∈ (Finset.Ioc 1 Z).attach,
          Real.log ((Z : ℝ) / (q.val : ℝ)) *
            primitiveCharacterPolynomialMeanSquare q.val
              (show 1 < q.val from (Finset.mem_Ioc.mp q.property).1) s
              (fun n =>
                a n * (preSiftedHybridKernel δ (x - Real.log n) : ℂ)) ∂MeasureTheory.volume) ≤
      ∑ n ∈ s, ‖a n‖ ^ 2 * ((24 : ℝ) * n + 14 * (Z : ℝ) ^ 2 / δ) := by
  have hleft := integrable_preSiftedHybrid_localized_family Z s δ hδ a
  have hright := integrable_preSiftedHybrid_localized_coefficient_bound Z δ hδ s a
  calc
    (∫ x : ℝ,
          ∑ q ∈ (Finset.Ioc 1 Z).attach,
            Real.log ((Z : ℝ) / (q.val : ℝ)) *
              primitiveCharacterPolynomialMeanSquare q.val
                (show 1 < q.val from (Finset.mem_Ioc.mp q.property).1) s
                (fun n =>
                  a n * (preSiftedHybridKernel δ (x - Real.log n) : ℂ)) ∂MeasureTheory.volume) ≤
        ∫ x : ℝ,
          ∑ n ∈ s,
            ‖a n * (preSiftedHybridKernel δ (x - Real.log n) : ℂ)‖ ^ 2 *
              (24 * δ * n + 14 * (Z : ℝ) ^ 2) ∂MeasureTheory.volume :=
      by
      apply MeasureTheory.integral_mono_ae hleft hright
      exact
        Filter.Eventually.of_forall fun x =>
          preSiftedHybrid_localized_mean_square_le Z hZ δ hδ hδ' s hpos hprime x a
    _ ≤ ∑ n ∈ s, ‖a n‖ ^ 2 * ((24 : ℝ) * n + 14 * (Z : ℝ) ^ 2 / δ) :=
      integral_preSiftedHybrid_localized_coefficient_bound_le Z δ hδ s a

/--
Claim: the squared Fourier norm of a Schwartz map on a finite interval is at most its integral
over the whole real line.

Proof: rewrite the interval integral as an integral over a restricted measure and compare that
measure with Lebesgue measure, using integrability of the squared Schwartz norm.

Role: extends the frequency interval before applying Plancherel.
-/
theorem preSiftedHybridFourier_intervalIntegral_le_full (a b : ℝ) (hab : a ≤ b)
    (F : SchwartzMap ℝ ℂ) :
    (∫ ξ in a..b, ‖(FourierTransform.fourier F : ℝ → ℂ) ξ‖ ^ 2) ≤
      ∫ ξ : ℝ, ‖(FourierTransform.fourier F : ℝ → ℂ) ξ‖ ^ 2 := by
  let G : SchwartzMap ℝ ℂ := FourierTransform.fourier F
  let f : ℝ → ℝ := fun x => ‖G x‖ ^ 2
  have hnonneg : 0 ≤ᵐ[MeasureTheory.volume] f :=
    Filter.Eventually.of_forall fun x => sq_nonneg ‖G x‖
  rw [intervalIntegral.integral_of_le hab]
  exact
    MeasureTheory.integral_mono_measure MeasureTheory.Measure.restrict_le_self hnonneg
      (integrable_norm_sq_of_schwartz G)

/--
Claim: the height integral of the finite Dirichlet polynomial is at most `8π` times the squared
integral of its localized Schwartz sum.

Proof: combine the pointwise Fourier lower bound, the height-to-frequency change of variables,
the full-line integral comparison, and Schwartz Plancherel.

Role: provides the Fourier localization input for the pre-sifted hybrid large sieve.
-/
theorem preSiftedHybridDirichletPolynomial_intervalIntegral_le_eight_pi (δ T : ℝ) (hδ : 0 < δ)
    (hT : 0 ≤ T) (hδT : δ * T ≤ 1 / 4) (s : Finset ℕ) (c : ℕ → ℂ) :
    (∫ t in (-T)..T, ‖preSiftedHybridDirichletPolynomial s c t‖ ^ 2) ≤
      8 * Real.pi * (∫ x : ℝ, ‖preSiftedHybridLocalizedSchwartz δ hδ s c x‖ ^ 2) := by
  let F := preSiftedHybridLocalizedSchwartz δ hδ s c
  have hheight := preSiftedHybridDirichletPolynomial_intervalIntegral_le_fourier δ T hδ hT hδT s c
  have hfreq := preSiftedHybridFourier_intervalIntegral_eq_frequency T F
  have hπ : 0 < 2 * Real.pi := by positivity
  have hab : -(T / (2 * Real.pi)) ≤ T / (2 * Real.pi) := neg_le_self (div_nonneg hT (le_of_lt hπ))
  have hfreq_le :=
    preSiftedHybridFourier_intervalIntegral_le_full (-(T / (2 * Real.pi))) (T / (2 * Real.pi)) hab F
  calc
    (∫ t in (-T)..T, ‖preSiftedHybridDirichletPolynomial s c t‖ ^ 2) ≤
        4 * (∫ t in (-T)..T, ‖(FourierTransform.fourier F : ℝ → ℂ) (t / (2 * Real.pi))‖ ^ 2) :=
      hheight
    _ =
        4 *
          (2 * Real.pi *
            (∫ ξ in (-(T / (2 * Real.pi)))..(T / (2 * Real.pi)),
              ‖(FourierTransform.fourier F : ℝ → ℂ) ξ‖ ^ 2)) :=
      by rw [hfreq]
    _ ≤ 4 * (2 * Real.pi * (∫ ξ : ℝ, ‖(FourierTransform.fourier F : ℝ → ℂ) ξ‖ ^ 2)) := by
      exact
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hfreq_le (by positivity))
          (by positivity)
    _ = 8 * Real.pi * (∫ x : ℝ, ‖F x‖ ^ 2) := by
      rw [SchwartzMap.integral_norm_sq_fourier]
      ring

/--
Inputs: a modulus greater than one, a finite coefficient support, a positive height cutoff, and
a positive localization scale satisfying `δ*T ≤ 1/4`.

Claim: the height integral of the primitive-character mean square is bounded by `8π` times the
integrated localized primitive-character mean square.

Proof: expand the primitive-character sum, apply the Schwartz–Plancherel localization to each
character polynomial, and recombine the finite character sum under the real-line integral.

Role: connects the pointwise pre-sifted large-sieve estimate to a height-integrated family bound.
-/
theorem primitiveCharacterPolynomialMeanSquare_intervalIntegral_le_eight_pi {q : ℕ} (hq : 1 < q)
    (s : Finset ℕ) (δ T : ℝ) (hδ : 0 < δ) (hT : 0 ≤ T) (hδT : δ * T ≤ 1 / 4) (a : ℕ → ℂ) :
    (∫ t in (-T)..T,
        primitiveCharacterPolynomialMeanSquare q hq s
          (fun n => a n * Complex.exp ((-(t * Real.log n) : ℝ) * Complex.I))) ≤
      8 * Real.pi *
        (∫ x : ℝ,
          primitiveCharacterPolynomialMeanSquare q hq s
            (fun n =>
              a n * (preSiftedHybridKernel δ (x - Real.log n) : ℂ)) ∂MeasureTheory.volume) := by
  classical
  have hpolyCont (χ : DirichletCharacter ℂ q) :
    Continuous
      (fun t : ℝ => preSiftedHybridDirichletPolynomial s (fun n => a n * χ (n : ZMod q)) t) := by
    unfold preSiftedHybridDirichletPolynomial
    apply continuous_finsetSum
    intro n hn
    apply Continuous.mul continuous_const
    have harg : Continuous (fun t : ℝ => -(t * Real.log n)) :=
      (continuous_id.mul continuous_const).neg
    exact Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp harg).mul continuous_const)
  have hsum (χ : DirichletCharacter ℂ q) (t : ℝ) :
    ∑ n ∈ s, a n * Complex.exp ((-(t * Real.log n) : ℝ) * Complex.I) * χ (n : ZMod q) =
      preSiftedHybridDirichletPolynomial s (fun n => a n * χ (n : ZMod q)) t := by
    unfold preSiftedHybridDirichletPolynomial
    apply Finset.sum_congr rfl
    intro n hn
    ring
  have hmean (t : ℝ) :
    primitiveCharacterPolynomialMeanSquare q hq s
        (fun n => a n * Complex.exp ((-(t * Real.log n) : ℝ) * Complex.I)) =
      ∑ χ ∈ primitiveDirichletCharacterSet q,
        ‖preSiftedHybridDirichletPolynomial s (fun n => a n * χ (n : ZMod q)) t‖ ^ 2 := by
    unfold primitiveCharacterPolynomialMeanSquare
    apply Finset.sum_congr rfl
    intro χ hχ
    rw [Complex.normSq_eq_norm_sq]
    exact congrArg (fun z : ℂ => ‖z‖ ^ 2) (hsum χ t)
  have hlocal (x : ℝ) :
    primitiveCharacterPolynomialMeanSquare q hq s
        (fun n => a n * (preSiftedHybridKernel δ (x - Real.log n) : ℂ)) =
      ∑ χ ∈ primitiveDirichletCharacterSet q,
        ‖preSiftedHybridLocalizedSchwartz δ hδ s (fun n => a n * χ (n : ZMod q)) x‖ ^ 2 :=
    primitiveCharacterPolynomialMeanSquare_eq_localizedSchwartz_norm_sq hq s δ hδ x a
  have hlocalIntegral :
    (∫ x : ℝ,
        primitiveCharacterPolynomialMeanSquare q hq s
          (fun n => a n * (preSiftedHybridKernel δ (x - Real.log n) : ℂ)) ∂MeasureTheory.volume) =
      ∑ χ ∈ primitiveDirichletCharacterSet q,
        ∫ x : ℝ,
          ‖preSiftedHybridLocalizedSchwartz δ hδ s (fun n => a n * χ (n : ZMod q)) x‖ ^
            2 ∂MeasureTheory.volume := by
    rw [show
        (fun x : ℝ =>
            primitiveCharacterPolynomialMeanSquare q hq s
              (fun n => a n * (preSiftedHybridKernel δ (x - Real.log n) : ℂ))) =
          fun x =>
          ∑ χ ∈ primitiveDirichletCharacterSet q,
            ‖preSiftedHybridLocalizedSchwartz δ hδ s (fun n => a n * χ (n : ZMod q)) x‖ ^ 2
        from funext hlocal]
    rw [MeasureTheory.integral_finsetSum _
        (fun χ hχ =>
          integrable_norm_sq_of_schwartz
            (preSiftedHybridLocalizedSchwartz δ hδ s (fun n => a n * χ (n : ZMod q))))]
  have hheightSum :
    (∫ t in (-T)..T,
        primitiveCharacterPolynomialMeanSquare q hq s
          (fun n => a n * Complex.exp ((-(t * Real.log n) : ℝ) * Complex.I))) =
      ∑ χ ∈ primitiveDirichletCharacterSet q,
        ∫ t in (-T)..T,
          ‖preSiftedHybridDirichletPolynomial s (fun n => a n * χ (n : ZMod q)) t‖ ^ 2 := by
    rw [show
        (fun t : ℝ =>
            primitiveCharacterPolynomialMeanSquare q hq s
              (fun n => a n * Complex.exp ((-(t * Real.log n) : ℝ) * Complex.I))) =
          fun t =>
          ∑ χ ∈ primitiveDirichletCharacterSet q,
            ‖preSiftedHybridDirichletPolynomial s (fun n => a n * χ (n : ZMod q)) t‖ ^ 2
        from funext hmean]
    exact
      intervalIntegral.integral_finsetSum (s := primitiveDirichletCharacterSet q) (f := fun χ t =>
        ‖preSiftedHybridDirichletPolynomial s (fun n => a n * χ (n : ZMod q)) t‖ ^ 2)
        (fun χ hχ => (hpolyCont χ).norm.pow 2 |>.intervalIntegrable (-T) T)
  calc
    (∫ t in (-T)..T,
          primitiveCharacterPolynomialMeanSquare q hq s
            (fun n => a n * Complex.exp ((-(t * Real.log n) : ℝ) * Complex.I))) =
        ∑ χ ∈ primitiveDirichletCharacterSet q,
          ∫ t in (-T)..T,
            ‖preSiftedHybridDirichletPolynomial s (fun n => a n * χ (n : ZMod q)) t‖ ^ 2 :=
      hheightSum
    _ ≤
        ∑ χ ∈ primitiveDirichletCharacterSet q,
          8 * Real.pi *
            (∫ x : ℝ,
              ‖preSiftedHybridLocalizedSchwartz δ hδ s (fun n => a n * χ (n : ZMod q)) x‖ ^
                2 ∂MeasureTheory.volume) :=
      by
      apply Finset.sum_le_sum
      intro χ hχ
      exact
        preSiftedHybridDirichletPolynomial_intervalIntegral_le_eight_pi δ T hδ hT hδT s
          (fun n => a n * χ (n : ZMod q))
    _ =
        8 * Real.pi *
          ∫ x : ℝ,
            primitiveCharacterPolynomialMeanSquare q hq s
              (fun n =>
                a n * (preSiftedHybridKernel δ (x - Real.log n) : ℂ)) ∂MeasureTheory.volume :=
      by rw [← Finset.mul_sum, ← hlocalIntegral]

/--
Inputs: a sieve cutoff, a height cutoff at least one, positive finite support, and coefficients
whose prime factors on the support exceed the sieve cutoff.

Claim: the logarithmically weighted primitive-character mean square over the height interval is
bounded by `2048` times the coefficient energy with weight `n + Z^2*T`.

Proof: choose scale `δ = 1/(4T)`, apply the modulus-wise Fourier localization, then use the
integrated pointwise pre-sieved estimate and absorb the fixed constants using `π < 4`.

Role: provides the finite-support hybrid large-sieve estimate required by the zero-density
argument.
-/
theorem primitiveCharacterFamilyMeanSquare_preSifted_hybrid_interval (Z : ℕ) (hZ : 2 ≤ Z) (T : ℝ)
    (hT : 1 ≤ T) (s : Finset ℕ) (hpos : ∀ n ∈ s, 0 < n) (a : ℕ → ℂ)
    (hprime : ∀ n ∈ s, ∀ p, Nat.Prime p → p ∣ n → Z < p) :
    (∑ q ∈ (Finset.Ioc 1 Z).attach,
        Real.log ((Z : ℝ) / (q.val : ℝ)) *
          ∫ t in (-T)..T,
            primitiveCharacterPolynomialMeanSquare q.val
              (show 1 < q.val from (Finset.mem_Ioc.mp q.property).1) s
              (fun n => a n * Complex.exp ((-(t * Real.log n) : ℝ) * Complex.I))) ≤
      (2048 : ℝ) * ∑ n ∈ s, ‖a n‖ ^ 2 * ((n : ℝ) + (Z : ℝ) ^ 2 * T) := by
  let δ : ℝ := 1 / (4 * T)
  have hTpos : 0 < T := lt_of_lt_of_le (by norm_num only) hT
  have hδ : 0 < δ := by
    dsimp only [δ]
    exact one_div_pos.mpr (by positivity)
  have hδT : δ * T = 1 / 4 := by
    dsimp only [δ]
    rw [one_div]
    calc
      (4 * T)⁻¹ * T = ((4 * T)⁻¹ * (4 * T)) * (1 / 4) := by ring
      _ = 1 / 4 := by rw [inv_mul_cancel₀ (by positivity), one_mul]
  have hδle : δ ≤ 1 / 4 := by
    calc
      δ = δ * 1 := by rw [mul_one]
      _ ≤ δ * T := mul_le_mul_of_nonneg_left hT hδ.le
      _ = 1 / 4 := hδT
  have hδinv : δ⁻¹ = 4 * T := by
    dsimp only [δ]
    rw [one_div, inv_inv]
  have hloc := integral_preSiftedHybrid_localized_family_le Z hZ δ hδ hδle s hpos hprime a
  calc
    (∑ q ∈ (Finset.Ioc 1 Z).attach,
          Real.log ((Z : ℝ) / (q.val : ℝ)) *
            ∫ t in (-T)..T,
              primitiveCharacterPolynomialMeanSquare q.val
                (show 1 < q.val from (Finset.mem_Ioc.mp q.property).1) s
                (fun n => a n * Complex.exp ((-(t * Real.log n) : ℝ) * Complex.I))) ≤
        ∑ q ∈ (Finset.Ioc 1 Z).attach,
          Real.log ((Z : ℝ) / (q.val : ℝ)) *
            (8 * Real.pi *
              ∫ x : ℝ,
                primitiveCharacterPolynomialMeanSquare q.val
                  (show 1 < q.val from (Finset.mem_Ioc.mp q.property).1) s
                  (fun n =>
                    a n * (preSiftedHybridKernel δ (x - Real.log n) : ℂ)) ∂MeasureTheory.volume) :=
      by
      apply Finset.sum_le_sum
      intro q hq
      have hqdata := Finset.mem_Ioc.mp q.property
      have hqposN : 0 < q.val := Nat.zero_lt_of_lt hqdata.1
      have hqpos : 0 < (q.val : ℝ) := by exact_mod_cast hqposN
      have hweight : 0 ≤ Real.log ((Z : ℝ) / (q.val : ℝ)) :=
        Real.log_nonneg ((one_le_div hqpos).2 (by exact_mod_cast hqdata.2))
      exact
        mul_le_mul_of_nonneg_left
          (primitiveCharacterPolynomialMeanSquare_intervalIntegral_le_eight_pi
            (show 1 < q.val from hqdata.1) s δ T hδ hTpos.le hδT.le a)
          hweight
    _ =
        8 * Real.pi *
          (∫ x : ℝ,
            ∑ q ∈ (Finset.Ioc 1 Z).attach,
              Real.log ((Z : ℝ) / (q.val : ℝ)) *
                primitiveCharacterPolynomialMeanSquare q.val
                  (show 1 < q.val from (Finset.mem_Ioc.mp q.property).1) s
                  (fun n =>
                    a n * (preSiftedHybridKernel δ (x - Real.log n) : ℂ)) ∂MeasureTheory.volume) :=
      by
      calc
        (∑ q ∈ (Finset.Ioc 1 Z).attach,
              Real.log ((Z : ℝ) / (q.val : ℝ)) *
                (8 * Real.pi *
                  ∫ x : ℝ,
                    primitiveCharacterPolynomialMeanSquare q.val
                      (show 1 < q.val from (Finset.mem_Ioc.mp q.property).1) s
                      (fun n =>
                        a n *
                          (preSiftedHybridKernel δ (x - Real.log n) : ℂ)) ∂MeasureTheory.volume)) =
            ∑ q ∈ (Finset.Ioc 1 Z).attach,
              8 * Real.pi *
                (Real.log ((Z : ℝ) / (q.val : ℝ)) *
                  ∫ x : ℝ,
                    primitiveCharacterPolynomialMeanSquare q.val
                      (show 1 < q.val from (Finset.mem_Ioc.mp q.property).1) s
                      (fun n =>
                        a n *
                          (preSiftedHybridKernel δ (x - Real.log n) : ℂ)) ∂MeasureTheory.volume) :=
          by
          apply Finset.sum_congr rfl
          intro q hq
          ring
        _ =
            8 * Real.pi *
              (∑ q ∈ (Finset.Ioc 1 Z).attach,
                Real.log ((Z : ℝ) / (q.val : ℝ)) *
                  ∫ x : ℝ,
                    primitiveCharacterPolynomialMeanSquare q.val
                      (show 1 < q.val from (Finset.mem_Ioc.mp q.property).1) s
                      (fun n =>
                        a n *
                          (preSiftedHybridKernel δ (x - Real.log n) : ℂ)) ∂MeasureTheory.volume) :=
          by rw [Finset.mul_sum]
        _ =
            8 * Real.pi *
              ∫ x : ℝ,
                ∑ q ∈ (Finset.Ioc 1 Z).attach,
                  Real.log ((Z : ℝ) / (q.val : ℝ)) *
                    primitiveCharacterPolynomialMeanSquare q.val
                      (show 1 < q.val from (Finset.mem_Ioc.mp q.property).1) s
                      (fun n =>
                        a n *
                          (preSiftedHybridKernel δ (x - Real.log n) : ℂ)) ∂MeasureTheory.volume :=
          by rw [← integral_preSiftedHybrid_localized_family_eq Z s δ hδ a]
    _ ≤ 8 * Real.pi * (∑ n ∈ s, ‖a n‖ ^ 2 * ((24 : ℝ) * n + 14 * (Z : ℝ) ^ 2 / δ)) :=
      mul_le_mul_of_nonneg_left hloc (by positivity)
    _ ≤ (2048 : ℝ) * ∑ n ∈ s, ‖a n‖ ^ 2 * ((n : ℝ) + (Z : ℝ) ^ 2 * T) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro n hn
      have hnnonneg : 0 ≤ (n : ℝ) := by positivity
      have hzT : 0 ≤ (Z : ℝ) ^ 2 * T := mul_nonneg (sq_nonneg _) hTpos.le
      have hcoeff :
        192 * Real.pi * n + 448 * Real.pi * (Z : ℝ) ^ 2 * T ≤ 2048 * (n + (Z : ℝ) ^ 2 * T) := by
        have h1 : 192 * Real.pi ≤ 2048 := by nlinarith only [Real.pi_lt_four]
        have h2 : 448 * Real.pi ≤ 2048 := by nlinarith only [Real.pi_lt_four]
        calc
          192 * Real.pi * n + 448 * Real.pi * (Z : ℝ) ^ 2 * T =
              192 * Real.pi * n + 448 * Real.pi * ((Z : ℝ) ^ 2 * T) :=
            by ring
          _ ≤ 2048 * n + 2048 * ((Z : ℝ) ^ 2 * T) :=
            add_le_add (mul_le_mul_of_nonneg_right h1 hnnonneg) (mul_le_mul_of_nonneg_right h2 hzT)
          _ = 2048 * (n + (Z : ℝ) ^ 2 * T) := by ring
      have henergy : 0 ≤ ‖a n‖ ^ 2 := sq_nonneg _
      calc
        8 * Real.pi * (‖a n‖ ^ 2 * ((24 : ℝ) * n + 14 * (Z : ℝ) ^ 2 / δ)) =
            ‖a n‖ ^ 2 * (192 * Real.pi * n + 112 * Real.pi * (Z : ℝ) ^ 2 / δ) :=
          by ring
        _ = ‖a n‖ ^ 2 * (192 * Real.pi * n + 448 * Real.pi * (Z : ℝ) ^ 2 * T) := by
          rw [div_eq_mul_inv, hδinv]
          ring
        _ ≤ ‖a n‖ ^ 2 * (2048 * (n + (Z : ℝ) ^ 2 * T)) := mul_le_mul_of_nonneg_left hcoeff henergy
        _ = 2048 * (‖a n‖ ^ 2 * (n + (Z : ℝ) ^ 2 * T)) := by ring

/--
Inputs: the parameters and hypotheses of
`primitiveCharacterFamilyMeanSquare_preSifted_hybrid_interval`.

Claim: the logarithmically weighted primitive-character mean square over the closed height
interval `[-T,T]` satisfies the same absolute hybrid bound.

Proof: identify the closed-interval integral with the interval integral; endpoints have zero
Lebesgue measure.

Role: exposes the set-integral form used by the zero-density application.
-/
theorem primitiveCharacterFamilyMeanSquare_preSifted_hybrid (Z : ℕ) (hZ : 2 ≤ Z) (T : ℝ)
    (hT : 1 ≤ T) (s : Finset ℕ) (hpos : ∀ n ∈ s, 0 < n) (a : ℕ → ℂ)
    (hprime : ∀ n ∈ s, ∀ p, Nat.Prime p → p ∣ n → Z < p) :
    (∑ q ∈ (Finset.Ioc 1 Z).attach,
        Real.log ((Z : ℝ) / (q.val : ℝ)) *
          ∫ t in Set.Icc (-T) T,
            primitiveCharacterPolynomialMeanSquare q.val
              (show 1 < q.val from (Finset.mem_Ioc.mp q.property).1) s
              (fun n =>
                a n * Complex.exp ((-(t * Real.log n) : ℝ) * Complex.I)) ∂MeasureTheory.volume) ≤
      (2048 : ℝ) * ∑ n ∈ s, ‖a n‖ ^ 2 * ((n : ℝ) + (Z : ℝ) ^ 2 * T) := by
  have hinterval : -T ≤ T := by linarith only [hT]
  have hset (q : { q // q ∈ Finset.Ioc 1 Z }) :
    (∫ t in Set.Icc (-T) T,
        primitiveCharacterPolynomialMeanSquare q.val
          (show 1 < q.val from (Finset.mem_Ioc.mp q.property).1) s
          (fun n =>
            a n * Complex.exp ((-(t * Real.log n) : ℝ) * Complex.I)) ∂MeasureTheory.volume) =
      ∫ t in (-T)..T,
        primitiveCharacterPolynomialMeanSquare q.val
          (show 1 < q.val from (Finset.mem_Ioc.mp q.property).1) s
          (fun n => a n * Complex.exp ((-(t * Real.log n) : ℝ) * Complex.I)) := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hinterval]
  calc
    (∑ q ∈ (Finset.Ioc 1 Z).attach,
          Real.log ((Z : ℝ) / (q.val : ℝ)) *
            ∫ t in Set.Icc (-T) T,
              primitiveCharacterPolynomialMeanSquare q.val
                (show 1 < q.val from (Finset.mem_Ioc.mp q.property).1) s
                (fun n =>
                  a n * Complex.exp ((-(t * Real.log n) : ℝ) * Complex.I)) ∂MeasureTheory.volume) =
        ∑ q ∈ (Finset.Ioc 1 Z).attach,
          Real.log ((Z : ℝ) / (q.val : ℝ)) *
            ∫ t in (-T)..T,
              primitiveCharacterPolynomialMeanSquare q.val
                (show 1 < q.val from (Finset.mem_Ioc.mp q.property).1) s
                (fun n => a n * Complex.exp ((-(t * Real.log n) : ℝ) * Complex.I)) :=
      by
      apply Finset.sum_congr rfl
      intro q hq
      rw [hset q]
    _ ≤ (2048 : ℝ) * ∑ n ∈ s, ‖a n‖ ^ 2 * ((n : ℝ) + (Z : ℝ) ^ 2 * T) :=
      primitiveCharacterFamilyMeanSquare_preSifted_hybrid_interval Z hZ T hT s hpos a hprime

/--
Inputs: an integer conductor cutoff `R`, a height cutoff, finite Dirichlet coefficients, and the
roughness condition above `R^2`.
Claim: after restricting the logarithmically weighted hybrid estimate at `Z = R^2` to conductors
at most `R`, the unweighted mean square gains a factor `1 / log R`.
Proof: on the restricted conductor set, `log (R^2 / q) ≥ log R`; discard the remaining terms
using nonnegativity of the mean squares and their logarithmic weights.
Role: gives the zero-density argument the unweighted conductor range with an explicit logarithmic
saving.
-/
theorem primitiveCharacterFamilyMeanSquare_preSifted_hybrid_R_squared (R : ℕ) (hR : 2 ≤ R) (T : ℝ)
    (hT : 1 ≤ T) (s : Finset ℕ) (hpos : ∀ n ∈ s, 0 < n) (a : ℕ → ℂ)
    (hprime : ∀ n ∈ s, ∀ p, Nat.Prime p → p ∣ n → R ^ 2 < p) :
    (∑ q ∈ ((Finset.Ioc 1 (R ^ 2)).attach.filter fun q => q.val ≤ R),
        ∫ t in Set.Icc (-T) T,
          primitiveCharacterPolynomialMeanSquare q.val
            (show 1 < q.val from (Finset.mem_Ioc.mp q.property).1) s
            (fun n =>
              a n * Complex.exp ((-(t * Real.log n) : ℝ) * Complex.I)) ∂MeasureTheory.volume) ≤
      (2048 : ℝ) / Real.log R * ∑ n ∈ s, ‖a n‖ ^ 2 * ((n : ℝ) + (R : ℝ) ^ 4 * T) := by
  classical
  let qBig := (Finset.Ioc 1 (R ^ 2)).attach
  let qSmall := qBig.filter fun q => q.val ≤ R
  let G (q : { q // q ∈ Finset.Ioc 1 (R ^ 2) }) : ℝ :=
    ∫ t in Set.Icc (-T) T,
      primitiveCharacterPolynomialMeanSquare q.val
        (show 1 < q.val from (Finset.mem_Ioc.mp q.property).1) s
        (fun n => a n * Complex.exp ((-(t * Real.log n) : ℝ) * Complex.I)) ∂MeasureTheory.volume
  have hR2 : 2 ≤ R ^ 2 := by nlinarith only [hR]
  have hbig := primitiveCharacterFamilyMeanSquare_preSifted_hybrid (R ^ 2) hR2 T hT s hpos a hprime
  have hRpos : (0 : ℝ) < R := by exact_mod_cast (by omega : 0 < R)
  have hlogR : 0 < Real.log R := by
    apply Real.log_pos
    exact_mod_cast hR
  have hGnonneg : ∀ q ∈ qBig, 0 ≤ G q := by
    intro q hq
    unfold G
    apply MeasureTheory.integral_nonneg
    intro t
    exact
      primitiveCharacterPolynomialMeanSquare_nonneg
        (show 1 < q.val from (Finset.mem_Ioc.mp q.property).1) s
        (fun n => a n * Complex.exp ((-(t * Real.log n) : ℝ) * Complex.I))
  have hlogWeight : ∀ q ∈ qSmall, Real.log R ≤ Real.log ((R : ℝ) ^ 2 / q.val) := by
    intro q hq
    have hmem : q ∈ qBig := (Finset.mem_filter.mp hq).1
    have hqR : (q.val : ℝ) ≤ R := by exact_mod_cast (Finset.mem_filter.mp hq).2
    have hqpos : (0 : ℝ) < q.val := by
      exact_mod_cast (Nat.zero_lt_of_lt (Finset.mem_Ioc.mp q.property).1)
    have hdiv : (1 : ℝ) ≤ (R : ℝ) / q.val := (one_le_div hqpos).2 hqR
    have hratio : (R : ℝ) ≤ (R : ℝ) ^ 2 / q.val := by
      calc
        (R : ℝ) = (R : ℝ) * 1 := by ring
        _ ≤ (R : ℝ) * ((R : ℝ) / q.val) := mul_le_mul_of_nonneg_left hdiv hRpos.le
        _ = (R : ℝ) ^ 2 / q.val := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          ring
    exact Real.log_le_log hRpos hratio
  have hsumBound :
    Real.log R * (∑ q ∈ qSmall, G q) ≤
      (2048 : ℝ) * ∑ n ∈ s, ‖a n‖ ^ 2 * ((n : ℝ) + (R : ℝ) ^ 4 * T) := by
    calc
      Real.log R * (∑ q ∈ qSmall, G q) = ∑ q ∈ qSmall, Real.log R * G q := by rw [Finset.mul_sum]
      _ ≤ ∑ q ∈ qSmall, Real.log ((R : ℝ) ^ 2 / q.val) * G q := by
        apply Finset.sum_le_sum
        intro q hq
        exact mul_le_mul_of_nonneg_right (hlogWeight q hq) (hGnonneg q (Finset.mem_filter.mp hq).1)
      _ ≤ ∑ q ∈ qBig, Real.log ((R : ℝ) ^ 2 / q.val) * G q := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro q hq hnot
        apply mul_nonneg
        · apply Real.log_nonneg
          have hqpos : (0 : ℝ) < q.val := by
            exact_mod_cast (Nat.zero_lt_of_lt (Finset.mem_Ioc.mp q.property).1)
          apply (one_le_div hqpos).2
          exact_mod_cast (Finset.mem_Ioc.mp q.property).2
        · exact hGnonneg q hq
      _ ≤ (2048 : ℝ) * ∑ n ∈ s, ‖a n‖ ^ 2 * ((n : ℝ) + (R : ℝ) ^ 4 * T) := by
        have hcastSq : ((R : ℝ) ^ 2) ^ 2 = (R : ℝ) ^ 4 := by ring
        simpa only [qBig, G, Nat.cast_pow, hcastSq] using hbig
  calc
    ∑ q ∈ qSmall, G q = (Real.log R * ∑ q ∈ qSmall, G q) / Real.log R := by
      rw [mul_div_cancel_left₀ _ (ne_of_gt hlogR)]
    _ ≤ ((2048 : ℝ) * ∑ n ∈ s, ‖a n‖ ^ 2 * ((n : ℝ) + (R : ℝ) ^ 4 * T)) / Real.log R :=
      div_le_div_of_nonneg_right hsumBound hlogR.le
    _ = (2048 : ℝ) / Real.log R * ∑ n ∈ s, ‖a n‖ ^ 2 * ((n : ℝ) + (R : ℝ) ^ 4 * T) := by ring

/--
Inputs: a conductor parameter `R`, a height interval with `1 ≤ T ≤ 2R`, and a finite set of
primes all at least `R^6`.
Claim: the corresponding logarithmically weighted prime Dirichlet polynomial has mean square at
most `4096 / log R` times the prime sum of `(log p)^2 / p`.
Proof: apply the `Z = R^2` hybrid estimate, use primality to verify its roughness condition, and
absorb `R^4 T` into each prime using the lower support bound.
Role: supplies the prime-polynomial form required by the zero-density argument.
-/
theorem primitiveCharacterPrimePolynomial_preSifted_hybrid_R_squared (R : ℕ) (hR : 2 ≤ R) (T : ℝ)
    (hT : 1 ≤ T) (hTupper : T ≤ 2 * R) (s : Finset ℕ) (hprime : ∀ p ∈ s, Nat.Prime p)
    (hlower : ∀ p ∈ s, R ^ 6 ≤ p) :
    (∑ q ∈ ((Finset.Ioc 1 (R ^ 2)).attach.filter fun q => q.val ≤ R),
        ∫ t in Set.Icc (-T) T,
          primitiveCharacterPolynomialMeanSquare q.val
            (show 1 < q.val from (Finset.mem_Ioc.mp q.property).1) s
            (fun p =>
              ((Real.log (p : ℝ) / (p : ℝ) : ℝ) : ℂ) *
                Complex.exp ((-(t * Real.log p) : ℝ) * Complex.I)) ∂MeasureTheory.volume) ≤
      (4096 : ℝ) / Real.log R * ∑ p ∈ s, (Real.log (p : ℝ)) ^ 2 / (p : ℝ) := by
  classical
  let a : ℕ → ℂ := fun p => ((Real.log (p : ℝ) / (p : ℝ) : ℝ) : ℂ)
  have hRgt : 1 < R := by omega
  have hR2ltR6 : R ^ 2 < R ^ 6 := Nat.pow_lt_pow_right hRgt (by omega : 2 < 6)
  have hrough : ∀ p ∈ s, ∀ r, Nat.Prime r → r ∣ p → R ^ 2 < r := by
    intro p hp r hr hdiv
    rcases (Nat.dvd_prime (hprime p hp)).mp hdiv with hrone | hrp
    · subst r
      exact False.elim (Nat.not_prime_one hr)
    · subst r
      exact lt_of_lt_of_le hR2ltR6 (hlower p hp)
  have hpos : ∀ p ∈ s, 0 < p := by
    intro p hp
    exact (hprime p hp).pos
  have hhybrid :=
    primitiveCharacterFamilyMeanSquare_preSifted_hybrid_R_squared R hR T hT s hpos a hrough
  have hRreal : (2 : ℝ) ≤ R := by exact_mod_cast hR
  have hR4T : (R : ℝ) ^ 4 * T ≤ (R : ℝ) ^ 6 := by
    calc
      (R : ℝ) ^ 4 * T ≤ (R : ℝ) ^ 4 * (2 * R) := mul_le_mul_of_nonneg_left hTupper (by positivity)
      _ = 2 * (R : ℝ) ^ 5 := by ring
      _ ≤ R * (R : ℝ) ^ 5 := mul_le_mul_of_nonneg_right hRreal (by positivity)
      _ = (R : ℝ) ^ 6 := by ring
  have henergy :
    ∀ p ∈ s, ‖a p‖ ^ 2 * ((p : ℝ) + (R : ℝ) ^ 4 * T) ≤ 2 * (Real.log (p : ℝ)) ^ 2 / (p : ℝ) := by
    intro p hp
    have hpReal : (0 : ℝ) < p := by exact_mod_cast (hprime p hp).pos
    have hplarge : (R : ℝ) ^ 6 ≤ p := by exact_mod_cast hlower p hp
    have hR4Tp : (R : ℝ) ^ 4 * T ≤ p := le_trans hR4T hplarge
    have hsum : (p : ℝ) + (R : ℝ) ^ 4 * T ≤ 2 * p := by linarith only [hR4Tp]
    have hnorm : ‖a p‖ ^ 2 = (Real.log (p : ℝ) / p) ^ 2 := by
      simp only [a, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [hnorm]
    calc
      (Real.log (p : ℝ) / p) ^ 2 * ((p : ℝ) + (R : ℝ) ^ 4 * T) ≤
          (Real.log (p : ℝ) / p) ^ 2 * (2 * p) :=
        mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
      _ = 2 * (Real.log (p : ℝ)) ^ 2 / p := by
        rw [div_pow]
        calc
          (Real.log (p : ℝ)) ^ 2 / p ^ 2 * (2 * p) = (Real.log (p : ℝ)) ^ 2 * (2 * p) / p ^ 2 := by
            rw [div_mul_eq_mul_div]
          _ = (p : ℝ) * (2 * (Real.log (p : ℝ)) ^ 2) / ((p : ℝ) * p) := by ring
          _ = 2 * (Real.log (p : ℝ)) ^ 2 / p := mul_div_mul_left _ _ (ne_of_gt hpReal)
  have henergySum :
    (∑ p ∈ s, ‖a p‖ ^ 2 * ((p : ℝ) + (R : ℝ) ^ 4 * T)) ≤
      2 * ∑ p ∈ s, (Real.log (p : ℝ)) ^ 2 / (p : ℝ) := by
    calc
      _ ≤ ∑ p ∈ s, 2 * (Real.log (p : ℝ)) ^ 2 / (p : ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        exact henergy p hp
      _ = 2 * ∑ p ∈ s, (Real.log (p : ℝ)) ^ 2 / (p : ℝ) := by
        calc
          _ = ∑ p ∈ s, 2 * ((Real.log (p : ℝ)) ^ 2 / (p : ℝ)) := by
            apply Finset.sum_congr rfl
            intro p hp
            ring
          _ = _ := by rw [Finset.mul_sum]
  change
    (∑ q ∈ ((Finset.Ioc 1 (R ^ 2)).attach.filter fun q => q.val ≤ R),
        ∫ t in Set.Icc (-T) T,
          primitiveCharacterPolynomialMeanSquare q.val
            (show 1 < q.val from (Finset.mem_Ioc.mp q.property).1) s
            (fun p =>
              a p * Complex.exp ((-(t * Real.log p) : ℝ) * Complex.I)) ∂MeasureTheory.volume) ≤
      _
  calc
    _ ≤ (2048 : ℝ) / Real.log R * ∑ p ∈ s, ‖a p‖ ^ 2 * ((p : ℝ) + (R : ℝ) ^ 4 * T) := hhybrid
    _ ≤ (2048 : ℝ) / Real.log R * (2 * ∑ p ∈ s, (Real.log (p : ℝ)) ^ 2 / (p : ℝ)) :=
      mul_le_mul_of_nonneg_left henergySum (by positivity)
    _ = (4096 : ℝ) / Real.log R * ∑ p ∈ s, (Real.log (p : ℝ)) ^ 2 / (p : ℝ) := by ring

/--
Inputs: integers `P₀ < u`, a cutoff `R` with `R^6 ≤ P₀`, and `1 ≤ T ≤ 2R`.
Claim: the prime polynomial supported on `P₀ < p ≤ u` satisfies the `4096 / log R` hybrid
mean-square bound.
Proof: filter the finite interval by primality and apply the finite prime-support estimate.
Role: exposes the interval-indexed form used for truncated prime sums in zero detection.
-/
theorem primitiveCharacterPrimeInterval_preSifted_hybrid_R_squared (R P₀ u : ℕ) (hR : 2 ≤ R)
    (hP₀ : R ^ 6 ≤ P₀) (T : ℝ) (hT : 1 ≤ T) (hTupper : T ≤ 2 * R) :
    (∑ q ∈ ((Finset.Ioc 1 (R ^ 2)).attach.filter fun q => q.val ≤ R),
        ∫ t in Set.Icc (-T) T,
          primitiveCharacterPolynomialMeanSquare q.val
            (show 1 < q.val from (Finset.mem_Ioc.mp q.property).1)
            ((Finset.Ioc P₀ u).filter Nat.Prime)
            (fun p =>
              ((Real.log (p : ℝ) / (p : ℝ) : ℝ) : ℂ) *
                Complex.exp ((-(t * Real.log p) : ℝ) * Complex.I)) ∂MeasureTheory.volume) ≤
      (4096 : ℝ) / Real.log R *
        ∑ p ∈ (Finset.Ioc P₀ u).filter Nat.Prime, (Real.log (p : ℝ)) ^ 2 / (p : ℝ) := by
  classical
  apply
    primitiveCharacterPrimePolynomial_preSifted_hybrid_R_squared R hR T hT hTupper
      ((Finset.Ioc P₀ u).filter Nat.Prime)
  · intro p hp
    exact (Finset.mem_filter.mp hp).2
  · intro p hp
    exact le_trans hP₀ (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).1.le

/--
Inputs: a natural upper endpoint for a finite prime sum.
Claim: the reciprocal logarithmic prime sum equals its Abel transform against Chebyshev's theta
function.
Proof: apply finite Abel summation with the reciprocal weight and identify each partial prime-log
sum with `Chebyshev.theta`.
Role: supplies the analytic identity used to derive the prime-weight energy bound for the hybrid
zero-density estimate.
-/
theorem finite_prime_log_reciprocal_sum_eq_abel (n : ℕ) (hn : 1 ≤ n) :
    (∑ k ∈ Finset.Ioc 1 n, if Nat.Prime k then Real.log (k : ℝ) / k else 0) =
      Chebyshev.theta n / n + ∫ t in Set.Ioc (1 : ℝ) n, (t ^ 2)⁻¹ * Chebyshev.theta t := by
  let c : ℕ → ℝ := fun k => if Nat.Prime k then Real.log k else 0
  let f : ℝ → ℝ := fun x => x⁻¹
  have hdiff : ∀ t ∈ Set.Icc (1 : ℝ) n, DifferentiableAt ℝ f t := by
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1)
    exact ((hasDerivAt_id t).inv ht0).differentiableAt
  have hsqcont : ContinuousOn (fun t : ℝ => (t ^ 2)⁻¹) (Set.Icc (1 : ℝ) n) := by
    apply ContinuousOn.inv₀ (continuousOn_id.pow 2)
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1)
    exact pow_ne_zero 2 ht0
  have hderivcont : ContinuousOn (deriv f) (Set.Icc (1 : ℝ) n) := by
    change ContinuousOn (fun t : ℝ => deriv (fun x : ℝ => x⁻¹) t) _
    convert hsqcont.neg using 1
    ext t
    simp only [deriv_inv, Pi.neg_apply]
  have hint : MeasureTheory.IntegrableOn (deriv f) (Set.Icc (1 : ℝ) n) :=
    ContinuousOn.integrableOn_compact isCompact_Icc hderivcont
  have habel :=
    sum_mul_eq_sub_sub_integral_mul (c := c) (a := (1 : ℝ)) (b := n) (by norm_num only)
      (by exact_mod_cast hn) hdiff hint
  have hcSum (x : ℝ) : (∑ k ∈ Finset.Icc 0 ⌊x⌋₊, c k) = Chebyshev.theta x := by
    dsimp only [c]
    rw [Chebyshev.theta_eq_sum_primesLE, Nat.primesLE_eq_filter_Icc_zero]
    simp only [Finset.sum_filter]
  have hthetaOne : Chebyshev.theta (1 : ℝ) = 0 :=
    Chebyshev.theta_eq_zero_of_le_one (by norm_num only)
  have hsumN : (∑ k ∈ Finset.Icc 0 n, c k) = Chebyshev.theta n := by
    simpa only [Nat.floor_natCast] using hcSum (n : ℝ)
  have hsumOne : (∑ k ∈ Finset.Icc 0 1, c k) = 0 := by
    simpa only [Nat.floor_natCast, Nat.floor_one, hthetaOne] using hcSum (1 : ℝ)
  have hleft :
    (∑ k ∈ Finset.Ioc 1 n, if Nat.Prime k then Real.log (k : ℝ) / k else 0) =
      ∑ k ∈ Finset.Ioc 1 n, f k * c k := by
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hprime : Nat.Prime k
    · dsimp only [f, c]
      rw [ite_eq_left hprime, ite_eq_left hprime]
      ring_nf
    · dsimp only [f, c]
      rw [ite_eq_right hprime, ite_eq_right hprime]
      simp only [mul_zero]
  have hintegral :
    (∫ t in Set.Ioc (1 : ℝ) n, deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) =
      ∫ t in Set.Ioc (1 : ℝ) n, deriv f t * Chebyshev.theta t := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with t
    exact congrArg (fun y : ℝ => deriv f t * y) (hcSum t)
  have hkernel :
    (∫ t in Set.Ioc (1 : ℝ) n, deriv f t * Chebyshev.theta t) =
      -(∫ t in Set.Ioc (1 : ℝ) n, (t ^ 2)⁻¹ * Chebyshev.theta t) := by
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    calc
      _ = ∫ t in (1 : ℝ)..n, deriv f t * Chebyshev.theta t :=
        (intervalIntegral.integral_of_le hn').symm
      _ = ∫ t in (1 : ℝ)..n, -((t ^ 2)⁻¹ * Chebyshev.theta t) := by
        apply intervalIntegral.integral_congr
        intro t ht
        change deriv (fun x : ℝ => x⁻¹) t * Chebyshev.theta t = _
        rw [deriv_inv]
        ring
      _ = -(∫ t in (1 : ℝ)..n, (t ^ 2)⁻¹ * Chebyshev.theta t) := intervalIntegral.integral_neg
      _ = -(∫ t in Set.Ioc (1 : ℝ) n, (t ^ 2)⁻¹ * Chebyshev.theta t) := by
        rw [intervalIntegral.integral_of_le hn']
  norm_num only [Nat.floor_natCast, Nat.floor_one] at habel
  rw [← hleft, hsumN, hsumOne] at habel
  rw [hintegral] at habel
  rw [hkernel] at habel
  convert habel using 1
  ring

/--
Inputs: a natural upper endpoint at least two.
Claim: the finite sum of prime logarithms divided by their primes is bounded by Chebyshev's
constant times `1 + log n`.
Proof: apply the Abel identity, Chebyshev's pointwise bound, and the integral of `1 / t`.
Role: supplies the first-order estimate used to bound the prime logarithmic energy in the hybrid
large-sieve specialization.
-/
theorem finite_prime_log_reciprocal_sum_le (n : ℕ) (hn : 2 ≤ n) :
    (∑ k ∈ Finset.Ioc 1 n, if Nat.Prime k then Real.log (k : ℝ) / k else 0) ≤
      Real.log 4 * (1 + Real.log n) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega)
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le (by norm_num only) hn1
  have hthetaInt : IntervalIntegrable Chebyshev.theta MeasureTheory.volume (1 : ℝ) n :=
    Chebyshev.theta_mono.intervalIntegrable
  have hpointNonzero (t : ℝ) (ht : t ∈ Set.uIcc (1 : ℝ) n) : t ≠ 0 := by
    rw [Set.uIcc_of_le hn1] at ht
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1)
  have hkernelCont : ContinuousOn (fun t : ℝ => (t ^ 2)⁻¹) (Set.uIcc (1 : ℝ) n) := by
    apply ContinuousOn.inv₀ (continuousOn_id.pow 2)
    intro t ht
    exact pow_ne_zero 2 (hpointNonzero t ht)
  have hinvCont : ContinuousOn (fun t : ℝ => t⁻¹) (Set.uIcc (1 : ℝ) n) := by
    apply ContinuousOn.inv₀ continuousOn_id
    exact hpointNonzero
  have hleftInt :
    IntervalIntegrable (fun t : ℝ => (t ^ 2)⁻¹ * Chebyshev.theta t) MeasureTheory.volume 1 n :=
    hthetaInt.continuousOn_mul hkernelCont
  have hrightInt : IntervalIntegrable (fun t : ℝ => Real.log 4 * t⁻¹) MeasureTheory.volume 1 n :=
    (continuousOn_const.mul hinvCont).intervalIntegrable
  have hpointwise : ∀ t ∈ Set.Icc (1 : ℝ) n, (t ^ 2)⁻¹ * Chebyshev.theta t ≤ Real.log 4 * t⁻¹ := by
    intro t ht
    have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
    have htheta := Chebyshev.theta_le_log4_mul_x (le_of_lt htpos)
    have hkernel : 0 ≤ (t ^ 2)⁻¹ := inv_nonneg.mpr (sq_nonneg t)
    calc
      (t ^ 2)⁻¹ * Chebyshev.theta t ≤ (t ^ 2)⁻¹ * (Real.log 4 * t) :=
        mul_le_mul_of_nonneg_left htheta hkernel
      _ = Real.log 4 * t⁻¹ := by field_simp [ne_of_gt htpos]
  have hintegral := intervalIntegral.integral_mono_on hn1 hleftInt hrightInt hpointwise
  have hintegral' :
    (∫ t in (1 : ℝ)..n, (t ^ 2)⁻¹ * Chebyshev.theta t) ≤ Real.log 4 * Real.log n := by
    calc
      (∫ t in (1 : ℝ)..n, (t ^ 2)⁻¹ * Chebyshev.theta t) ≤ ∫ t in (1 : ℝ)..n, Real.log 4 * t⁻¹ :=
        hintegral
      _ = Real.log 4 * Real.log n := by
        rw [intervalIntegral.integral_const_mul, integral_inv_of_pos (by norm_num only) hnpos]
        simp only [div_one]
  have hthetaN := Chebyshev.theta_le_log4_mul_x (show (0 : ℝ) ≤ n by positivity)
  have hfirst : Chebyshev.theta n / n ≤ Real.log 4 := by
    apply (div_le_iff₀ hnpos).2
    simpa only [mul_comm] using hthetaN
  have habel := finite_prime_log_reciprocal_sum_eq_abel n (by omega)
  rw [← intervalIntegral.integral_of_le hn1] at habel
  calc
    _ = Chebyshev.theta n / n + ∫ t in (1 : ℝ)..n, (t ^ 2)⁻¹ * Chebyshev.theta t := habel
    _ ≤ Real.log 4 + Real.log 4 * Real.log n := add_le_add hfirst hintegral'
    _ = Real.log 4 * (1 + Real.log n) := by ring

/--
Inputs: a natural upper endpoint at least two.
Claim: the finite sum of squared prime logarithms divided by their primes is bounded by
`log 4 * log n * (1 + log n)`.
Proof: bound one factor of each squared logarithm by `log n` and apply the reciprocal-logarithm
sum estimate.
Role: supplies the coefficient-energy bound needed by the prime-supported hybrid estimate.
-/
theorem finite_prime_log_square_reciprocal_sum_le (n : ℕ) (hn : 2 ≤ n) :
    (∑ k ∈ Finset.Ioc 1 n, if Nat.Prime k then Real.log (k : ℝ) ^ 2 / k else 0) ≤
      Real.log 4 * Real.log n * (1 + Real.log n) := by
  have hn1 : 1 ≤ n := by omega
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
  have hpoint (k : ℕ) (hk : k ∈ Finset.Ioc 1 n) :
    (if Nat.Prime k then Real.log (k : ℝ) ^ 2 / k else 0) ≤
      Real.log n * (if Nat.Prime k then Real.log (k : ℝ) / k else 0) := by
    by_cases hprime : Nat.Prime k
    · have hk1 : 1 ≤ k := by
        have hkin : 1 < k := (Finset.mem_Ioc.mp hk).1
        omega
      have hkpos : (0 : ℝ) < k := by exact_mod_cast hprime.pos
      have hklog : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by exact_mod_cast hk1)
      have hlogle : Real.log (k : ℝ) ≤ Real.log n :=
        Real.log_le_log hkpos (by exact_mod_cast (Finset.mem_Ioc.mp hk).2)
      have hsq : Real.log (k : ℝ) ^ 2 ≤ Real.log n * Real.log (k : ℝ) := by
        nlinarith only [hlogle, hklog]
      rw [ite_eq_left hprime, ite_eq_left hprime]
      calc
        Real.log (k : ℝ) ^ 2 / k ≤ (Real.log n * Real.log (k : ℝ)) / k :=
          div_le_div_of_nonneg_right hsq (le_of_lt hkpos)
        _ = Real.log n * (Real.log (k : ℝ) / k) := by ring
    · rw [ite_eq_right hprime, ite_eq_right hprime]
      simp only [mul_zero, le_refl]
  calc
    _ ≤ ∑ k ∈ Finset.Ioc 1 n, Real.log n * (if Nat.Prime k then Real.log (k : ℝ) / k else 0) := by
      apply Finset.sum_le_sum
      intro k hk
      exact hpoint k hk
    _ = Real.log n * (∑ k ∈ Finset.Ioc 1 n, if Nat.Prime k then Real.log (k : ℝ) / k else 0) := by
      rw [Finset.mul_sum]
    _ ≤ Real.log n * (Real.log 4 * (1 + Real.log n)) :=
      mul_le_mul_of_nonneg_left (finite_prime_log_reciprocal_sum_le n hn) hlogn
    _ = Real.log 4 * Real.log n * (1 + Real.log n) := by ring

/--
Inputs: the hybrid range parameters, a prime interval with lower endpoint at least `R ^ 6`, and
the condition that the interval is nonempty.
Claim: the interval hybrid mean square is bounded using only the logarithmic size of its upper
endpoint.
Proof: extend the prime energy sum to all primes up to `u`, then apply the finite prime
log-square estimate.
Role: supplies the logarithmic-energy form needed when the hybrid estimate enters zero detection.
-/
theorem primitiveCharacterPrimeInterval_preSifted_hybrid_log_square_bound (R P₀ u : ℕ) (hR : 2 ≤ R)
    (hP₀ : R ^ 6 ≤ P₀) (hP₀u : P₀ ≤ u) (T : ℝ) (hT : 1 ≤ T) (hTupper : T ≤ 2 * R) :
    (∑ q ∈ ((Finset.Ioc 1 (R ^ 2)).attach.filter fun q => q.val ≤ R),
        ∫ t in Set.Icc (-T) T,
          primitiveCharacterPolynomialMeanSquare q.val
            (show 1 < q.val from (Finset.mem_Ioc.mp q.property).1)
            ((Finset.Ioc P₀ u).filter Nat.Prime)
            (fun p =>
              ((Real.log (p : ℝ) / (p : ℝ) : ℝ) : ℂ) *
                Complex.exp ((-(t * Real.log p) : ℝ) * Complex.I)) ∂MeasureTheory.volume) ≤
      (4096 : ℝ) / Real.log R * (Real.log 4 * Real.log u * (1 + Real.log u)) := by
  have hRpos : 0 < R := by omega
  have hRpow : 2 ≤ R ^ 6 := by
    calc
      2 ≤ R := hR
      _ ≤ R ^ 6 := Nat.le_self_pow (by norm_num only) R
  have hu : 2 ≤ u := le_trans hRpow (le_trans hP₀ hP₀u)
  have hP₀pos : 0 < P₀ := lt_of_lt_of_le (Nat.pow_pos hRpos) hP₀
  have hP₀one : 1 ≤ P₀ := by omega
  let s := (Finset.Ioc P₀ u).filter Nat.Prime
  let t := Finset.Ioc 1 u
  let w : ℕ → ℝ := fun p => if Nat.Prime p then Real.log (p : ℝ) ^ 2 / p else 0
  have hsubset : s ⊆ t := by
    intro p hp
    have hpI := (Finset.mem_filter.mp hp).1
    rcases Finset.mem_Ioc.mp hpI with ⟨hpP₀, hpu⟩
    exact Finset.mem_Ioc.mpr ⟨by omega, hpu⟩
  have hsumS : (∑ p ∈ s, (Real.log (p : ℝ)) ^ 2 / p) = ∑ p ∈ s, w p := by
    apply Finset.sum_congr rfl
    intro p hp
    have hprime := (Finset.mem_filter.mp hp).2
    change Real.log (p : ℝ) ^ 2 / p = if Nat.Prime p then Real.log (p : ℝ) ^ 2 / p else 0
    rw [ite_eq_left hprime]
  have hsumSubset : (∑ p ∈ s, w p) ≤ ∑ p ∈ t, w p := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
    intro p hp _
    by_cases hprime : Nat.Prime p
    · change 0 ≤ if Nat.Prime p then Real.log (p : ℝ) ^ 2 / p else 0
      rw [ite_eq_left hprime]
      exact div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
    · change 0 ≤ if Nat.Prime p then Real.log (p : ℝ) ^ 2 / p else 0
      rw [ite_eq_right hprime]
  have henergy := finite_prime_log_square_reciprocal_sum_le u hu
  have hcoefficient : 0 ≤ (4096 : ℝ) / Real.log R := by
    apply div_nonneg (by norm_num only)
    exact (Real.log_pos (by exact_mod_cast (show 1 < R by omega))).le
  have hhybrid :=
    primitiveCharacterPrimeInterval_preSifted_hybrid_R_squared R P₀ u hR hP₀ T hT hTupper
  calc
    _ ≤ (4096 : ℝ) / Real.log R * ∑ p ∈ s, (Real.log (p : ℝ)) ^ 2 / p := hhybrid
    _ ≤ (4096 : ℝ) / Real.log R * ∑ p ∈ t, w p := by
      rw [hsumS]
      exact mul_le_mul_of_nonneg_left hsumSubset hcoefficient
    _ ≤ (4096 : ℝ) / Real.log R * (Real.log 4 * Real.log u * (1 + Real.log u)) :=
      mul_le_mul_of_nonneg_left henergy hcoefficient

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity
