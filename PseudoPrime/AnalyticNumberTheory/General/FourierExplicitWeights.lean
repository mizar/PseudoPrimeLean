/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.MellinInversion
public import Mathlib.Topology.Algebra.Support

/-!
# Logarithmic weights for the Fourier explicit formula

Transform identities used in Iwaniec--Kowalski, Theorem 5.12: reflection of even
logarithmic weights, Mellin-to-Fourier conversion, and the complex pole frequency.
These results do not assume or prove the underlying L-function explicit formula.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.General

/-- The logarithmic test weight phi(x)=x^(-1/2)*g(log x), defined using real
exponential scaling. On positive x this is g(log x)/sqrt x, the arithmetic weight
in the Fourier form of the explicit formula. -/
noncomputable def logarithmicTestWeight (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  Real.exp (-Real.log x / 2) • g (Real.log x)

/-- The logarithmic test weight at exp(u) is exp(-u/2)*g(u).
Use log(exp(u))=u; this is the logarithmic-coordinate substitution. -/
theorem logarithmicTestWeight_exp (g : ℝ → ℂ) (u : ℝ) :
    logarithmicTestWeight g (Real.exp u) = Real.exp (-u / 2) • g u := by
  rw [logarithmicTestWeight, Real.log_exp]

/-- For an even test function, the critical-line Mellin pullback is exactly g.
Cancel the two opposite real exponential factors and use evenness.
This identifies the Fourier normalization on Re(s)=1/2. -/
theorem logarithmicTestWeight_critical_pullback (g : ℝ → ℂ) (he : ∀ u : ℝ, g (-u) = g u) (u : ℝ) :
    Real.exp (-(1 / 2 : ℝ) * u) • logarithmicTestWeight g (Real.exp (-u)) = g u := by
  rw [logarithmicTestWeight_exp, he, smul_smul, ← Real.exp_add]
  have hz : -(1 / 2 : ℝ) * u + - -u / 2 = 0 := by ring
  rw [hz, Real.exp_zero, one_smul]

/-- For any even complex test function, its logarithmic weight has Mellin value
at 1/2+I*t equal to the usual Fourier transform at t/(2*pi).
Apply the Mellin-to-Fourier change of variables and cancel the critical-line weight.
This identity alone does not assert convergence of an L-function explicit formula. -/
theorem mellin_logarithmicTestWeight_criticalLine (g : ℝ → ℂ) (he : ∀ u : ℝ, g (-u) = g u) (t : ℝ) :
    mellin (logarithmicTestWeight g) (((1 / 2 : ℝ) : ℂ) + Complex.I * t) =
      FourierTransform.fourier g (t / (2 * Real.pi)) := by
  rw [mellin_eq_fourier]
  have hr : ((((1 / 2 : ℝ) : ℂ) + Complex.I * t) : ℂ).re = (1 / 2 : ℝ) := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
  have hi : ((((1 / 2 : ℝ) : ℂ) + Complex.I * t) : ℂ).im = t := by
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, zero_mul, one_mul, zero_add]
  rw [hr, hi]
  have hf :
    (fun u : ℝ => Real.exp (-(1 / 2 : ℝ) * u) • logarithmicTestWeight g (Real.exp (-u))) = g := by
    funext u
    exact logarithmicTestWeight_critical_pullback g he u
  rw [hf]

/-- The logarithmic weight at one equals g(0).
Its exponential factor is one, identifying the conductor coefficient in the explicit formula. -/
theorem logarithmicTestWeight_one (g : ℝ → ℂ) : logarithmicTestWeight g 1 = g 0 := by
  simp only [logarithmicTestWeight, Real.log_one, neg_zero, zero_div, Real.exp_zero, one_smul]

/-- For even g and positive x, the reflected weight x^(-1)*phi(x^(-1)) equals phi(x).
Use log(x^(-1))=-log x and combine exponential factors.
This combines the original and dual arithmetic sums in the Fourier explicit formula. -/
theorem logarithmicTestWeight_reflection (g : ℝ → ℂ) (he : ∀ u : ℝ, g (-u) = g u) {x : ℝ}
    (hx : 0 < x) : x⁻¹ • logarithmicTestWeight g x⁻¹ = logarithmicTestWeight g x := by
  rw [logarithmicTestWeight, Real.log_inv, he, smul_smul, logarithmicTestWeight]
  have hxexp : x⁻¹ = Real.exp (-Real.log x) := by rw [Real.exp_neg, Real.exp_log hx]
  rw [hxexp, ← Real.exp_add]
  congr 2
  ring

/-- For positive x, the logarithmic test weight is g(log x)/sqrt x.
Express sqrt x as exp(log x/2) and invert the positive exponential.
This recovers the original theorem's arithmetic weight. -/
theorem logarithmicTestWeight_eq_div_sqrt (g : ℝ → ℂ) {x : ℝ} (hx : 0 < x) :
    logarithmicTestWeight g x = g (Real.log x) / (Real.sqrt x : ℂ) := by
  have hs : Real.sqrt x = Real.exp (Real.log x / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx]
    congr 1
    ring
  rw [logarithmicTestWeight, show -Real.log x / 2 = -(Real.log x / 2) by ring, Real.exp_neg, ← hs,
    Complex.real_smul, Complex.ofReal_inv]
  rw [div_eq_mul_inv, mul_comm]

/-- For even g, the Mellin pullback at real part sigma is
exp((1/2-sigma)*u)*g(u). Combine the exponential scalings after logarithmic substitution.
The noncentral factor makes the extra exponential integrability requirement explicit. -/
theorem logarithmicTestWeight_pullback (g : ℝ → ℂ) (he : ∀ u : ℝ, g (-u) = g u) (σ u : ℝ) :
    Real.exp (-σ * u) • logarithmicTestWeight g (Real.exp (-u)) =
      Real.exp (((1 / 2 : ℝ) - σ) * u) • g u := by
  rw [logarithmicTestWeight_exp, he, smul_smul, ← Real.exp_add]
  congr 2
  ring

/-- The Mellin transform of an even logarithmic weight at s is the ordinary Fourier
transform of exp((1/2-Re(s))*u)*g(u) at Im(s)/(2*pi).
Use the general Mellin-to-Fourier formula. Off the critical line, Schwartz decay alone
does not guarantee integrability of this exponentially weighted function. -/
theorem mellin_logarithmicTestWeight (g : ℝ → ℂ) (he : ∀ u : ℝ, g (-u) = g u) (s : ℂ) :
    mellin (logarithmicTestWeight g) s =
      FourierTransform.fourier (fun u : ℝ => Real.exp (((1 / 2 : ℝ) - s.re) * u) • g u)
        (s.im / (2 * Real.pi)) := by
  rw [mellin_eq_fourier]
  have hf :
    (fun u : ℝ => Real.exp (-s.re * u) • logarithmicTestWeight g (Real.exp (-u))) =
      (fun u : ℝ => Real.exp (((1 / 2 : ℝ) - s.re) * u) • g u) := by
    funext u
    exact logarithmicTestWeight_pullback g he s.re u
  rw [hf]

/-- The complex-frequency Fourier integral of g with kernel exp(-2*pi*I*z*y).
For real z it is the ordinary Fourier transform. Compact support and continuity ensure
integrability for every complex z; this definition alone does not assert convergence. -/
noncomputable def fourierLaplace (g : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ y : ℝ, Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * z * y) * g y

/-- At real frequency, the Fourier-Laplace integral equals mathlib's Fourier transform.
Identify the exponential kernels pointwise, checking the two-pi normalization and sign. -/
theorem fourierLaplace_real (g : ℝ → ℂ) (t : ℝ) :
    fourierLaplace g t = FourierTransform.fourier g t := by
  rw [fourierLaplace, Real.fourier_eq']
  apply MeasureTheory.integral_congr_ae
  exact
    MeasureTheory.ae_of_all _
      (fun y => by
        change
          Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * t * y) * g y =
            Complex.exp ((-2 * Real.pi * inner ℝ y t : ℝ) * Complex.I) • g y
        rw [smul_eq_mul]
        congr 2
        simp only [Real.inner_apply, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_ofNat]
        ring)

/-- The Fourier-Laplace transform of an even test function is even in complex frequency.
Change y to -y using reflection invariance of real volume and compare kernels.
This identifies the two signs of the pole's imaginary frequency. -/
theorem fourierLaplace_neg (g : ℝ → ℂ) (he : ∀ y : ℝ, g (-y) = g y) (z : ℂ) :
    fourierLaplace g (-z) = fourierLaplace g z := by
  rw [fourierLaplace, fourierLaplace]
  have h :=
    MeasureTheory.integral_neg_eq_self
      (fun y : ℝ => Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * z * y) * g y) MeasureTheory.volume
  rw [← h]
  apply MeasureTheory.integral_congr_ae
  exact
    MeasureTheory.ae_of_all _
      (fun y => by
        change
          Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * (-z) * y) * g y =
            Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * z * ((-y : ℝ) : ℂ)) * g (-y)
        rw [he, Complex.ofReal_neg]
        congr 2
        ring)

/-- A continuous compactly supported complex test function has an integrable
Fourier-Laplace integrand at every complex frequency. The exponential multiplier is
continuous and preserves compact support; this justifies complex-frequency evaluations. -/
theorem integrable_fourierLaplace_integrand (g : ℝ → ℂ) (hg : Continuous g)
    (hs : HasCompactSupport g) (z : ℂ) :
    MeasureTheory.Integrable
      (fun y : ℝ => Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * z * y) * g y) := by
  have hc : Continuous (fun y : ℝ => Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * z * y)) :=
    Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  exact (hc.mul hg).integrable_of_hasCompactSupport hs.mul_left

/-- At complex z, the Fourier-Laplace integral is the ordinary Fourier transform
of exp(2*pi*Im(z)*y)*g(y) at Re(z). Split the complex exponential into oscillatory
and real exponential factors. This exposes the needed exponential moment. -/
theorem fourierLaplace_eq_weighted_fourier (g : ℝ → ℂ) (z : ℂ) :
    fourierLaplace g z =
      FourierTransform.fourier (fun y : ℝ => Real.exp (2 * Real.pi * z.im * y) • g y) z.re := by
  rw [fourierLaplace, Real.fourier_eq']
  apply MeasureTheory.integral_congr_ae
  exact
    MeasureTheory.ae_of_all _
      (fun y => by
        change
          Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * z * y) * g y =
            Complex.exp ((-2 * Real.pi * inner ℝ y z.re : ℝ) * Complex.I) •
              (Real.exp (2 * Real.pi * z.im * y) • g y)
        rw [Complex.real_smul, smul_eq_mul, ← mul_assoc, Complex.ofReal_exp, ← Complex.exp_add]
        congr 2
        nth_rw 1 [← Complex.re_add_im z]
        simp only [Real.inner_apply, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_ofNat]
        ring_nf
        rw [Complex.I_sq]
        ring)

/-- The complex Fourier frequency associated with Mellin parameter s:
Im(s)/(2*pi)+I*(1/2-Re(s))/(2*pi), equivalently (s-1/2)/(2*pi*I).
It is real on the critical line and imaginary at the pole s=1. -/
noncomputable def mellinFourierFrequency (s : ℂ) : ℂ :=
  (s.im / (2 * Real.pi) : ℝ) + Complex.I * ((1 / 2 - s.re) / (2 * Real.pi) : ℝ)

/-- The associated Fourier frequency has real part Im(s)/(2*pi).
Compute the real part of its defining affine expression. -/
theorem mellinFourierFrequency_re (s : ℂ) :
    (mellinFourierFrequency s).re = s.im / (2 * Real.pi) := by
  simp only [mellinFourierFrequency, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]

/-- The associated Fourier frequency has imaginary part (1/2-Re(s))/(2*pi).
Compute the imaginary part; it controls exponential weighting off the critical line. -/
theorem mellinFourierFrequency_im (s : ℂ) :
    (mellinFourierFrequency s).im = (1 / 2 - s.re) / (2 * Real.pi) := by
  simp only [mellinFourierFrequency, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, zero_mul, one_mul, zero_add]

/-- For an even test function, the Mellin transform of its logarithmic weight equals
the Fourier-Laplace transform at the associated complex frequency.
Match the exponentially weighted Fourier representations and cancel nonzero two pi.
This translates both central-line integrals and off-line zero terms. -/
theorem mellin_logarithmicTestWeight_eq_fourierLaplace (g : ℝ → ℂ) (he : ∀ y : ℝ, g (-y) = g y)
    (s : ℂ) : mellin (logarithmicTestWeight g) s = fourierLaplace g (mellinFourierFrequency s) := by
  rw [mellin_logarithmicTestWeight g he, fourierLaplace_eq_weighted_fourier,
    mellinFourierFrequency_re, mellinFourierFrequency_im]
  have hc :=
    div_mul_cancel₀ (1 / 2 - s.re) (mul_ne_zero (show (2 : ℝ) ≠ 0 by norm_num only) Real.pi_ne_zero)
  have hf :
    (fun u : ℝ => Real.exp (((1 / 2 : ℝ) - s.re) * u) • g u) =
      (fun u : ℝ => Real.exp (2 * Real.pi * ((1 / 2 - s.re) / (2 * Real.pi)) * u) • g u) := by
    funext u
    congr 2
    rw [mul_comm (2 * Real.pi) ((1 / 2 - s.re) / (2 * Real.pi)), hc]
  rw [hf]

/-- The Mellin pole s=1 corresponds to Fourier frequency -I/(4*pi).
Compute its real and imaginary parts; evenness permits the positive sign in the final formula. -/
theorem mellinFourierFrequency_one :
    mellinFourierFrequency 1 = -(Complex.I * ((1 / (4 * Real.pi) : ℝ) : ℂ)) := by
  apply Complex.ext
  · rw [mellinFourierFrequency_re]
    simp only [Complex.one_im, zero_div, Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, neg_zero]
  · rw [mellinFourierFrequency_im]
    simp only [Complex.one_re, Complex.neg_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, zero_add]
    ring

/-- For even g, the Mellin value of its logarithmic weight at s=1 equals its
Fourier-Laplace value at I/(4*pi). Combine the complex-frequency transform identity
with evenness. Convergence requires an appropriate test class, such as compact support. -/
theorem mellin_logarithmicTestWeight_one (g : ℝ → ℂ) (he : ∀ y : ℝ, g (-y) = g y) :
    mellin (logarithmicTestWeight g) 1 =
      fourierLaplace g (Complex.I * ((1 / (4 * Real.pi) : ℝ) : ℂ)) := by
  rw [mellin_logarithmicTestWeight_eq_fourierLaplace g he, mellinFourierFrequency_one,
    fourierLaplace_neg g he]

end PseudoPrime.AnalyticNumberTheory.General
