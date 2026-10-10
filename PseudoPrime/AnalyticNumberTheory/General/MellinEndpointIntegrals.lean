/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.General.MellinTestInversion
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Mellin evaluation of endpoint resolvents

A Laplace representation of reciprocal linear factors has an integrable
product majorant. Fubini and Mellin inversion evaluate each resolvent
integral as a positive logarithmic-coordinate tail of the test weight.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.General

/-- For a complex s with positive real part, the positive-half-line integral
of exp(-s*u) is 1/s. Apply the complex exponential improper integral.
This is the Laplace representation of an endpoint resolvent. -/
theorem integral_exp_neg_complex_Ioi {s : ℂ} (hs : 0 < s.re) :
    (∫ u : ℝ in Set.Ioi 0, Complex.exp (-s * u)) = 1 / s := by
  have hn : (-s).re < 0 := by
    rw [Complex.neg_re]
    exact neg_neg_of_pos hs
  simpa only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, neg_div_neg_eq] using
    integral_exp_mul_complex_Ioi hn 0

/-- For a continuous weight vertically integrable on real part sigma, with
real r below sigma, its product with exp(-(sigma+iT-r)*u) is integrable
on positive u and all T. Its norm factors as a decaying real exponential
in u times the weight norm in T, giving an integrable product majorant.
This proves the Fubini premise for endpoint resolvent evaluation. -/
theorem integrable_mellin_resolvent_laplace_weight (W : ℂ → ℂ) (hW : Continuous W) (σ r : ℝ)
    (hs : r < σ) (hw : Complex.VerticalIntegrable W σ) :
    MeasureTheory.Integrable
      (fun p : ℝ × ℝ ↦
        Complex.exp (-(((σ : ℂ) + p.2 * Complex.I) - r) * p.1) * W ((σ : ℂ) + p.2 * Complex.I))
      ((MeasureTheory.volume.restrict (Set.Ioi 0)).prod MeasureTheory.volume) := by
  have hd : r - σ < 0 := sub_neg.mpr hs
  have hmajor := (integrableOn_exp_mul_Ioi hd 0).mul_prod hw.norm
  have hline : Continuous (fun p : ℝ × ℝ ↦ (σ : ℂ) + p.2 * Complex.I) :=
    continuous_const.add ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)
  have hexp : Continuous (fun p : ℝ × ℝ ↦ Complex.exp (-(((σ : ℂ) + p.2 * Complex.I) - r) * p.1)) :=
    Complex.continuous_exp.comp
      (((hline.sub continuous_const).neg).mul (Complex.continuous_ofReal.comp continuous_fst))
  apply hmajor.mono' (hexp.mul (hW.comp hline)).aestronglyMeasurable
  exact
    MeasureTheory.ae_of_all _ fun p ↦ by
      dsimp only [Pi.mul_apply, Function.comp_apply]
      simp only [norm_mul, Complex.norm_exp, Complex.mul_re, Complex.neg_re, Complex.sub_re,
        Complex.add_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
        zero_mul, sub_zero, add_zero]
      have heq : -(σ - r) * p.1 = (r - σ) * p.1 := by ring
      rw [heq]

/-- For a continuous vertically integrable weight and a real pole below the
vertical line, the integral of W(s)/(s-r) equals the iterated Laplace-weight
integral over positive logarithmic coordinates. Use absolute product
integrability to exchange the integrals and evaluate the exponential tail.
This connects the rational endpoint kernel to Mellin inversion. -/
theorem integral_mellin_resolvent_eq_iterated_laplace (W : ℂ → ℂ) (hW : Continuous W) (σ r : ℝ)
    (hs : r < σ) (hw : Complex.VerticalIntegrable W σ) :
    (∫ T : ℝ, W ((σ : ℂ) + T * Complex.I) / (((σ : ℂ) + T * Complex.I) - r)) =
      ∫ u : ℝ in Set.Ioi 0,
        ∫ T : ℝ,
          Complex.exp (-(((σ : ℂ) + T * Complex.I) - r) * u) * W ((σ : ℂ) + T * Complex.I) := by
  rw [MeasureTheory.integral_integral_swap
      (integrable_mellin_resolvent_laplace_weight W hW σ r hs hw)]
  apply MeasureTheory.integral_congr_ae
  exact
    MeasureTheory.ae_of_all _ fun T ↦ by
      have hp : 0 < (((σ : ℂ) + T * Complex.I) - r).re := by
        simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
        exact sub_pos.mpr hs
      dsimp only
      rw [MeasureTheory.integral_mul_const, integral_exp_neg_complex_Ioi hp]
      ring

/-- For arbitrary complex s and real r,u, exp(-(s-r)*u) is exp(r*u)
times the Mellin inverse kernel at exp(u). Expand the positive real base
complex power using its logarithm. This factors the shifted Laplace kernel. -/
theorem exp_shift_eq_mellin_inverse_kernel (s : ℂ) (r u : ℝ) :
    Complex.exp (-(s - r) * u) = Complex.exp ((r : ℂ) * u) * (Real.exp u : ℂ) ^ (-s) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero u)), ←
    Complex.ofReal_log (Real.exp_pos u).le, Real.log_exp, ← Complex.exp_add]
  congr 1
  ring

/-- For an even smooth compact test, any real vertical line and real r,u,
the normalized shifted exponential Mellin integral evaluates to
exp(r*u) times the logarithmic weight at exp(u). Factor out exp(r*u)
and apply the proved Mellin inversion. This evaluates the inner integral
in the endpoint resolvent representation. -/
theorem normalized_integral_shifted_mellin_kernel (g : ℝ → ℂ) (he : ∀ u : ℝ, g (-u) = g u)
    (hc : HasCompactSupport g) (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g) (σ r u : ℝ) :
    (1 / (2 * Real.pi) : ℝ) •
        (∫ T : ℝ,
          Complex.exp (-(((σ : ℂ) + T * Complex.I) - r) * u) *
            mellin (logarithmicTestWeight g) ((σ : ℂ) + T * Complex.I)) =
      Complex.exp ((r : ℂ) * u) * logarithmicTestWeight g (Real.exp u) := by
  have hi := mellinInv_mellin_logarithmicTestWeight g he hc hg σ (Real.exp_pos u)
  rw [mellinInv] at hi
  simp only [smul_eq_mul] at hi
  have ht :
    (∫ T : ℝ,
        Complex.exp (-(((σ : ℂ) + T * Complex.I) - r) * u) *
          mellin (logarithmicTestWeight g) ((σ : ℂ) + T * Complex.I)) =
      Complex.exp ((r : ℂ) * u) *
        (∫ T : ℝ,
          (Real.exp u : ℂ) ^ (-((σ : ℂ) + T * Complex.I)) *
            mellin (logarithmicTestWeight g) ((σ : ℂ) + T * Complex.I)) := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    exact
      MeasureTheory.ae_of_all _ fun T ↦ by
        dsimp only
        rw [exp_shift_eq_mellin_inverse_kernel]
        ring
  rw [ht, ← mul_smul_comm, hi]

/-- For an even smooth compact test and a real pole r below a vertical line,
the normalized integral of its Mellin transform divided by s-r equals
the positive logarithmic-coordinate tail of exp(r*u)*phi(exp(u)).
Absolute Laplace-product integrability supplies Fubini, then Mellin inversion
evaluates the inner integral. This gives the endpoint contributions
without an independent interchange or inversion premise. -/
theorem normalized_integral_mellin_resolvent_eq_tail (g : ℝ → ℂ) (he : ∀ u : ℝ, g (-u) = g u)
    (hc : HasCompactSupport g) (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g) (σ r : ℝ) (hs : r < σ) :
    (1 / (2 * Real.pi) : ℝ) •
        (∫ T : ℝ,
          mellin (logarithmicTestWeight g) ((σ : ℂ) + T * Complex.I) /
            (((σ : ℂ) + T * Complex.I) - r)) =
      ∫ u : ℝ in Set.Ioi 0, Complex.exp ((r : ℂ) * u) * logarithmicTestWeight g (Real.exp u) := by
  rw [integral_mellin_resolvent_eq_iterated_laplace _
      (differentiable_mellin_logarithmicTestWeight g hc hg.continuous).continuous σ r hs
      (verticalIntegrable_mellin_logarithmicTestWeight g he hc hg σ),
    ← MeasureTheory.integral_smul]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro u _
  exact normalized_integral_shifted_mellin_kernel g he hc hg σ r u

/-- For any complex-valued real function, reflection identifies its negative-half-line
integral with the positive-half-line integral of f(-u). Apply invariance of volume
to the indicator. This splits logarithmic endpoint weights without a Jacobian factor. -/
private theorem integral_Iio_zero_eq_reflected_Ioi (f : ℝ → ℂ) :
    (∫ u : ℝ in Set.Iio 0, f u) = ∫ u : ℝ in Set.Ioi 0, f (-u) := by
  rw [← MeasureTheory.integral_indicator measurableSet_Iio, ←
    MeasureTheory.integral_neg_eq_self _ MeasureTheory.volume, ←
    MeasureTheory.integral_indicator measurableSet_Ioi]
  apply MeasureTheory.integral_congr_ae
  exact
    MeasureTheory.ae_of_all _ fun u ↦ by
      simp only [Set.indicator_apply, Set.mem_Iio, Set.mem_Ioi, neg_lt_zero]

/-- For a continuous compactly supported logarithmic test and any real exponential
weight, the weighted test is integrable. Continuity and preservation of compact
support under scalar multiplication prove this. It permits splitting endpoint tails. -/
theorem integrable_exponential_logarithmic_test (g : ℝ → ℂ) (hc : HasCompactSupport g)
    (hg : Continuous g) (a : ℝ) :
    MeasureTheory.Integrable (fun u : ℝ ↦ Real.exp (a * u) • g u) := by
  exact
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul
        hg |>.integrable_of_hasCompactSupport
      hc.smul_left

/-- For an even continuous compact test, the sum of its positive tails weighted by
exp(-u/2) and exp(u/2) equals the global exp(-u/2)-weighted integral. Reflect the
negative half-line and use evenness. This combines the two endpoint resolvents. -/
theorem logarithmic_endpoint_tails_eq_integral (g : ℝ → ℂ) (he : ∀ u : ℝ, g (-u) = g u)
    (hc : HasCompactSupport g) (hg : Continuous g) :
    (∫ u : ℝ in Set.Ioi 0, Real.exp (-u / 2) • g u) +
        (∫ u : ℝ in Set.Ioi 0, Real.exp (u / 2) • g u) =
      ∫ u : ℝ, Real.exp (-u / 2) • g u := by
  have hi : MeasureTheory.Integrable (fun u : ℝ ↦ Real.exp (-u / 2) • g u) := by
    apply (integrable_exponential_logarithmic_test g hc hg (-1 / 2)).congr
    exact
      MeasureTheory.ae_of_all _ fun u ↦ by
        dsimp only
        have h : (-1 / 2 : ℝ) * u = -u / 2 := by ring
        rw [h]
  have hs := intervalIntegral.integral_Iio_add_Ici (b := (0 : ℝ)) hi.integrableOn hi.integrableOn
  rw [MeasureTheory.integral_Ici_eq_integral_Ioi, integral_Iio_zero_eq_reflected_Ioi] at hs
  have hn :
    (∫ u : ℝ in Set.Ioi 0, Real.exp (-(-u) / 2) • g (-u)) =
      ∫ u : ℝ in Set.Ioi 0, Real.exp (u / 2) • g u := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro u _
    dsimp only
    rw [neg_neg, he]
  rw [hn, add_comm] at hs
  exact hs

/-- For an even test, its logarithmic weight has Mellin value at one equal to the
global exp(-u/2)-weighted integral. Evaluate the Mellin-to-Fourier identity at
zero frequency. This identifies the combined endpoint contribution. -/
theorem mellin_logarithmicTestWeight_one_eq_integral (g : ℝ → ℂ) (he : ∀ u : ℝ, g (-u) = g u) :
    mellin (logarithmicTestWeight g) 1 = ∫ u : ℝ, Real.exp (-u / 2) • g u := by
  rw [mellin_logarithmicTestWeight g he, Real.fourier_eq']
  simp only [Complex.one_re, Complex.one_im, zero_div, inner_zero_right, mul_zero,
    Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_smul]
  apply MeasureTheory.integral_congr_ae
  exact
    MeasureTheory.ae_of_all _ fun u ↦ by
      dsimp only
      have h : ((1 / 2 : ℝ) - 1) * u = -u / 2 := by ring
      rw [h]

/-- For a continuous vertically integrable weight, division by s-r remains integrable
on any real line sigma above r. Integrate the absolutely integrable Laplace product
in its positive coordinate. This justifies separating the two endpoint integrals. -/
theorem integrable_mellin_resolvent (W : ℂ → ℂ) (hW : Continuous W) (σ r : ℝ) (hs : r < σ)
    (hw : Complex.VerticalIntegrable W σ) :
    MeasureTheory.Integrable
      (fun T : ℝ ↦ W ((σ : ℂ) + T * Complex.I) / (((σ : ℂ) + T * Complex.I) - r)) := by
  apply (integrable_mellin_resolvent_laplace_weight W hW σ r hs hw).integral_prod_right.congr
  exact
    MeasureTheory.ae_of_all _ fun T ↦ by
      have hp : 0 < (((σ : ℂ) + T * Complex.I) - r).re := by
        simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
        exact sub_pos.mpr hs
      dsimp only
      rw [MeasureTheory.integral_mul_const, integral_exp_neg_complex_Ioi hp]
      ring

/-- For any logarithmic test and real r,u, exp(r*u)*phi(exp(u)) equals
exp((r-1/2)*u)*g(u). Use the logarithmic substitution and add the exponential
weights. This evaluates the tail integrands obtained from Laplace inversion. -/
theorem exp_mul_logarithmicTestWeight_exp (g : ℝ → ℂ) (r u : ℝ) :
    Complex.exp ((r : ℂ) * u) * logarithmicTestWeight g (Real.exp u) =
      Real.exp ((r - 1 / 2) * u) • g u := by
  rw [logarithmicTestWeight_exp, ← Complex.ofReal_mul, ← Complex.ofReal_exp]
  simp only [Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
  have h : r * u + -u / 2 = (r - 1 / 2) * u := by ring
  rw [h]

/-- For a continuous vertically integrable weight and a real line above one,
the endpoint kernel integral splits into the resolvents at zero and one.
Prove each resolvent integrable before using integral linearity. This separates
the endpoint factors in a regularized completion. -/
theorem integral_mellin_endpoint_kernel_eq_resolvents (W : ℂ → ℂ) (hW : Continuous W) (σ : ℝ)
    (hs : 1 < σ) (hw : Complex.VerticalIntegrable W σ) :
    (∫ T : ℝ,
        (1 / ((σ : ℂ) + T * Complex.I) + 1 / (((σ : ℂ) + T * Complex.I) - 1)) *
          W ((σ : ℂ) + T * Complex.I)) =
      (∫ T : ℝ, W ((σ : ℂ) + T * Complex.I) / ((σ : ℂ) + T * Complex.I)) +
        (∫ T : ℝ, W ((σ : ℂ) + T * Complex.I) / (((σ : ℂ) + T * Complex.I) - 1)) := by
  have hi0 := integrable_mellin_resolvent W hW σ 0 (lt_trans zero_lt_one hs) hw
  have hi1 := integrable_mellin_resolvent W hW σ 1 hs hw
  simp only [Complex.ofReal_zero, sub_zero, Complex.ofReal_one] at hi0 hi1
  rw [← MeasureTheory.integral_add hi0 hi1]
  apply MeasureTheory.integral_congr_ae
  exact
    MeasureTheory.ae_of_all _ fun T ↦ by
      dsimp only
      ring

/-- The zero-endpoint Laplace tail integrand of any logarithmic test is
exp(-u/2)*g(u). Substitute r=0 in the shifted-weight identity.
This is the first tail in the endpoint kernel evaluation. -/
private theorem logarithmicTestWeight_endpoint_zero (g : ℝ → ℂ) (u : ℝ) :
    Complex.exp ((0 : ℂ) * u) * logarithmicTestWeight g (Real.exp u) = Real.exp (-u / 2) • g u := by
  rw [← Complex.ofReal_zero, exp_mul_logarithmicTestWeight_exp]
  have h : ((0 : ℝ) - 1 / 2) * u = -u / 2 := by ring
  rw [h]

/-- The one-endpoint Laplace tail integrand of any logarithmic test is
exp(u/2)*g(u). Substitute r=1 in the shifted-weight identity.
This is the reflected tail in the endpoint kernel evaluation. -/
private theorem logarithmicTestWeight_endpoint_one (g : ℝ → ℂ) (u : ℝ) :
    Complex.exp ((1 : ℂ) * u) * logarithmicTestWeight g (Real.exp u) = Real.exp (u / 2) • g u := by
  rw [← Complex.ofReal_one, exp_mul_logarithmicTestWeight_exp]
  have h : ((1 : ℝ) - 1 / 2) * u = u / 2 := by ring
  rw [h]

/-- For an even smooth compact test and a real line above one, the normalized
integral of (1/s+1/(s-1))*Mellin(phi)(s) equals Mellin(phi)(1).
Laplace inversion evaluates the two resolvents; reflection combines their tails.
This evaluates one completion's endpoint regularization contribution. -/
theorem normalized_integral_mellin_endpoint_kernel (g : ℝ → ℂ) (he : ∀ u : ℝ, g (-u) = g u)
    (hc : HasCompactSupport g) (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g) (σ : ℝ) (hs : 1 < σ) :
    (1 / (2 * Real.pi) : ℝ) •
        (∫ T : ℝ,
          (1 / ((σ : ℂ) + T * Complex.I) + 1 / (((σ : ℂ) + T * Complex.I) - 1)) *
            mellin (logarithmicTestWeight g) ((σ : ℂ) + T * Complex.I)) =
      mellin (logarithmicTestWeight g) 1 := by
  rw [integral_mellin_endpoint_kernel_eq_resolvents _
      (differentiable_mellin_logarithmicTestWeight g hc hg.continuous).continuous σ hs
      (verticalIntegrable_mellin_logarithmicTestWeight g he hc hg σ),
    smul_add]
  have hr0 := normalized_integral_mellin_resolvent_eq_tail g he hc hg σ 0 (lt_trans zero_lt_one hs)
  have hr1 := normalized_integral_mellin_resolvent_eq_tail g he hc hg σ 1 hs
  simp only [Complex.ofReal_zero, sub_zero, Complex.ofReal_one] at hr0 hr1
  rw [hr0, hr1, mellin_logarithmicTestWeight_one_eq_integral g he]
  simp only [logarithmicTestWeight_endpoint_zero, logarithmicTestWeight_endpoint_one]
  exact logarithmic_endpoint_tails_eq_integral g he hc hg.continuous

/-- For an integer regularization order on a real vertical line, the conjugated
endpoint kernel at negative height equals the original kernel at positive height.
Conjugation fixes the real coefficients and reverses I. This evaluates the dual
endpoint contribution without assuming the test itself is real. -/
theorem star_reflected_endpoint_kernel (k : ℤ) (σ T : ℝ) :
    star ((k : ℂ) * (1 / ((σ : ℂ) + (-T) * Complex.I) + 1 / (((σ : ℂ) + (-T) * Complex.I) - 1))) =
      (k : ℂ) * (1 / ((σ : ℂ) + T * Complex.I) + 1 / (((σ : ℂ) + T * Complex.I) - 1)) := by
  simp only [Complex.star_def, map_mul, map_add, map_div₀, map_sub, map_intCast, map_one, map_neg,
    Complex.conj_ofReal, Complex.conj_I, neg_mul_neg]

/-- For an integer regularization order and an even smooth compact test on a line
above one, the normalized endpoint integral equals k*Mellin(phi)(1).
Factor out k and apply the endpoint-kernel evaluation. This is one completion's
regularization contribution to the Mellin explicit identity. -/
theorem normalized_integral_regularization_endpoint (k : ℤ) (g : ℝ → ℂ) (he : ∀ u : ℝ, g (-u) = g u)
    (hc : HasCompactSupport g) (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g) (σ : ℝ) (hs : 1 < σ) :
    (1 / (2 * Real.pi) : ℝ) •
        (∫ T : ℝ,
          ((k : ℂ) * (1 / ((σ : ℂ) + T * Complex.I) + 1 / (((σ : ℂ) + T * Complex.I) - 1))) *
            mellin (logarithmicTestWeight g) ((σ : ℂ) + T * Complex.I)) =
      (k : ℂ) * mellin (logarithmicTestWeight g) 1 := by
  simp only [mul_assoc]
  rw [MeasureTheory.integral_const_mul, ← mul_smul_comm,
    normalized_integral_mellin_endpoint_kernel g he hc hg σ hs]

/-- For an integer regularization order and an even smooth compact test on a line
above one, the original and reflected dual endpoint integrals sum to
2*k*Mellin(phi)(1). Conjugation identifies the dual rational kernel with the
original, then evaluate each integral. This tracks both endpoint contributions
before comparing the completed and ordinary zero sets in the source formula. -/
theorem normalized_integral_paired_regularization_endpoints (k : ℤ) (g : ℝ → ℂ)
    (he : ∀ u : ℝ, g (-u) = g u) (hc : HasCompactSupport g) (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g) (σ : ℝ)
    (hs : 1 < σ) :
    (1 / (2 * Real.pi) : ℝ) •
        ((∫ T : ℝ,
            ((k : ℂ) * (1 / ((σ : ℂ) + T * Complex.I) + 1 / (((σ : ℂ) + T * Complex.I) - 1))) *
              mellin (logarithmicTestWeight g) ((σ : ℂ) + T * Complex.I)) +
          (∫ T : ℝ,
            star
                ((k : ℂ) *
                  (1 / ((σ : ℂ) + (-T) * Complex.I) + 1 / (((σ : ℂ) + (-T) * Complex.I) - 1))) *
              mellin (logarithmicTestWeight g) ((σ : ℂ) + T * Complex.I))) =
      (2 * (k : ℂ)) * mellin (logarithmicTestWeight g) 1 := by
  simp only [star_reflected_endpoint_kernel]
  rw [smul_add, normalized_integral_regularization_endpoint k g he hc hg σ hs]
  ring

/-- For an integer regularization order and an even smooth compact test, the
endpoint-weighted Mellin integrand is integrable on a real line above one.
Combine the two integrable resolvents and multiply by the integer coefficient.
This permits separating endpoint terms from the gamma remainder. -/
theorem integrable_regularization_endpoint_mellin (k : ℤ) (g : ℝ → ℂ) (he : ∀ u : ℝ, g (-u) = g u)
    (hc : HasCompactSupport g) (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g) (σ : ℝ) (hs : 1 < σ) :
    MeasureTheory.Integrable
      (fun T : ℝ ↦
        ((k : ℂ) * (1 / ((σ : ℂ) + T * Complex.I) + 1 / (((σ : ℂ) + T * Complex.I) - 1))) *
          mellin (logarithmicTestWeight g) ((σ : ℂ) + T * Complex.I)) := by
  have hW := (differentiable_mellin_logarithmicTestWeight g hc hg.continuous).continuous
  have hw := verticalIntegrable_mellin_logarithmicTestWeight g he hc hg σ
  have hi0 := integrable_mellin_resolvent _ hW σ 0 (lt_trans zero_lt_one hs) hw
  have hi1 := integrable_mellin_resolvent _ hW σ 1 hs hw
  simp only [Complex.ofReal_zero, sub_zero, Complex.ofReal_one] at hi0 hi1
  apply ((hi0.add hi1).const_mul (k : ℂ)).congr
  exact
    MeasureTheory.ae_of_all _ fun T ↦ by
      dsimp only [Pi.add_apply, Pi.mul_apply]
      ring

end PseudoPrime.AnalyticNumberTheory.General
