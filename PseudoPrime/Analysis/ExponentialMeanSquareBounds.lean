/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.FiniteExponentialMeanSquare

/-!
# Cross terms and energy bounds

The energy of a difference is not a difference of energies. The exact cross term
and a safe factor-two estimate are available without any zero-distribution hypothesis.
-/

@[expose] public section

namespace PseudoPrime.Analysis.ExponentialMeanSquare

/-- For a fixed finite frequency set, subtraction of coefficients subtracts the sums.
Distribute the finite sum; this represents differences in the same finite function space. -/
theorem exponentialSum_sub {ι : Type*} (s : Finset ι) (γ : ι → ℝ) (a b : ι → ℂ) :
    exponentialSum s γ (fun j ↦ a j - b j) = fun v ↦
      exponentialSum s γ a v - exponentialSum s γ b v := by
  funext v
  simp only [exponentialSum, sub_mul, Finset.sum_sub_distrib]

/-- The squared-norm difference retains twice the real weighted cross product.
Expand the complex norm square and distribute the real weight for integration. -/
theorem energy_sub_integrand (f g : ℝ → ℂ) (v : ℝ) :
    ‖f v - g v‖ ^ 2 * weight v =
      ‖f v‖ ^ 2 * weight v + ‖g v‖ ^ 2 * weight v - 2 * (crossIntegrand f g v).re := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_sub, crossIntegrand, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  ring

/-- For complex numbers, the squared norm of a difference is bounded by twice both squares.
Use the nonnegative squares of the sums of the real and imaginary components. -/
theorem norm_sub_sq_le (z w : ℂ) : ‖z - w‖ ^ 2 ≤ 2 * ‖z‖ ^ 2 + 2 * ‖w‖ ^ 2 := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
  nlinarith only [sq_nonneg (z.re + w.re), sq_nonneg (z.im + w.im)]

/-- For integrable diagonal products and cross product, the difference energy has an exact
cross term.
Integrate the pointwise norm-square identity and commute real part with integration. -/
theorem energy_sub (f g : ℝ → ℂ) (hf : MeasureTheory.Integrable (fun v ↦ ‖f v‖ ^ 2 * weight v))
    (hg : MeasureTheory.Integrable (fun v ↦ ‖g v‖ ^ 2 * weight v))
    (hfg : MeasureTheory.Integrable (crossIntegrand f g)) :
    energy (fun v ↦ f v - g v) = energy f + energy g - 2 * (∫ v : ℝ, crossIntegrand f g v).re := by
  have hc : MeasureTheory.Integrable (fun v ↦ (crossIntegrand f g v).re) := by
    simpa only [RCLike.re_to_complex] using hfg.re
  have hs : MeasureTheory.Integrable (fun v ↦ ‖f v‖ ^ 2 * weight v + ‖g v‖ ^ 2 * weight v) := by
    simpa only [Pi.add_def] using hf.add hg
  simp only [energy, energy_sub_integrand]
  rw [MeasureTheory.integral_sub hs (hc.const_mul 2), MeasureTheory.integral_add hf hg,
    MeasureTheory.integral_const_mul]
  congr 2
  simpa only [RCLike.re_to_complex] using integral_re hfg

/-- For integrable weighted squares including the difference, the difference energy is bounded
by twice the two energies. Multiply the pointwise inequality by the positive weight and
integrate. -/
theorem energy_sub_le (f g : ℝ → ℂ) (hf : MeasureTheory.Integrable (fun v ↦ ‖f v‖ ^ 2 * weight v))
    (hg : MeasureTheory.Integrable (fun v ↦ ‖g v‖ ^ 2 * weight v))
    (hsub : MeasureTheory.Integrable (fun v ↦ ‖f v - g v‖ ^ 2 * weight v)) :
    energy (fun v ↦ f v - g v) ≤ 2 * energy f + 2 * energy g := by
  have hs :
    MeasureTheory.Integrable (fun v ↦ 2 * (‖f v‖ ^ 2 * weight v) + 2 * (‖g v‖ ^ 2 * weight v)) := by
    simpa only [Pi.add_def] using (hf.const_mul 2).add (hg.const_mul 2)
  have hi :=
    MeasureTheory.integral_mono hsub hs
      (fun v ↦
        show ‖f v - g v‖ ^ 2 * weight v ≤ 2 * (‖f v‖ ^ 2 * weight v) + 2 * (‖g v‖ ^ 2 * weight v)
          from by
          dsimp only [weight]
          nlinarith only [norm_sub_sq_le (f v) (g v), Real.exp_pos (-2 * |v|)])
  simpa only [MeasureTheory.integral_add (hf.const_mul 2) (hg.const_mul 2),
    MeasureTheory.integral_const_mul, energy] using hi

/-- For any two finite exponential sums, the difference energy retains its exact cross integral.
Apply the general identity using the already proved diagonal and cross integrability. -/
theorem energy_exponentialSum_sub {ι κ : Type*} (s : Finset ι) (r : Finset κ) (γ : ι → ℝ)
    (δ : κ → ℝ) (a : ι → ℂ) (b : κ → ℂ) :
    energy (fun v ↦ exponentialSum s γ a v - exponentialSum r δ b v) =
      energy (exponentialSum s γ a) + energy (exponentialSum r δ b) -
        2 * (∫ v : ℝ, crossIntegrand (exponentialSum s γ a) (exponentialSum r δ b) v).re := by
  exact
    energy_sub _ _ (integrable_energy_exponentialSum s γ a) (integrable_energy_exponentialSum r δ b)
      (integrable_cross_exponentialSum s r γ δ a b)

/-- If both weighted squares and their complex cross product are integrable, so is the
weighted square of their difference. Expand it into the three integrable terms. -/
theorem integrable_energy_sub (f g : ℝ → ℂ)
    (hf : MeasureTheory.Integrable (fun v ↦ ‖f v‖ ^ 2 * weight v))
    (hg : MeasureTheory.Integrable (fun v ↦ ‖g v‖ ^ 2 * weight v))
    (hfg : MeasureTheory.Integrable (crossIntegrand f g)) :
    MeasureTheory.Integrable (fun v ↦ ‖f v - g v‖ ^ 2 * weight v) := by
  have hc : MeasureTheory.Integrable (fun v ↦ (crossIntegrand f g v).re) := by
    simpa only [RCLike.re_to_complex] using hfg.re
  have hs : MeasureTheory.Integrable (fun v ↦ ‖f v‖ ^ 2 * weight v + ‖g v‖ ^ 2 * weight v) := by
    simpa only [Pi.add_def] using hf.add hg
  simpa only [← energy_sub_integrand] using hs.sub' (hc.const_mul 2)

/-- For any two finite exponential sums, the difference energy is at most twice their energies.
Derive difference integrability from the actual cross product, then integrate the norm bound. -/
theorem energy_exponentialSum_sub_le {ι κ : Type*} (s : Finset ι) (r : Finset κ) (γ : ι → ℝ)
    (δ : κ → ℝ) (a : ι → ℂ) (b : κ → ℂ) :
    energy (fun v ↦ exponentialSum s γ a v - exponentialSum r δ b v) ≤
      2 * energy (exponentialSum s γ a) + 2 * energy (exponentialSum r δ b) := by
  exact
    energy_sub_le _ _ (integrable_energy_exponentialSum s γ a)
      (integrable_energy_exponentialSum r δ b)
      (integrable_energy_sub _ _ (integrable_energy_exponentialSum s γ a)
        (integrable_energy_exponentialSum r δ b) (integrable_cross_exponentialSum s r γ δ a b))

/-- If two finite exponential sums have energy at most A, their difference has energy at most 4A.
Combine the factor-two energy estimate with the two supplied energy bounds. -/
theorem energy_exponentialSum_sub_le_four {ι κ : Type*} (s : Finset ι) (r : Finset κ) (γ : ι → ℝ)
    (δ : κ → ℝ) (a : ι → ℂ) (b : κ → ℂ) {A : ℝ} (hs : energy (exponentialSum s γ a) ≤ A)
    (hr : energy (exponentialSum r δ b) ≤ A) :
    energy (fun v ↦ exponentialSum s γ a v - exponentialSum r δ b v) ≤ 4 * A := by
  have h := energy_exponentialSum_sub_le s r γ δ a b
  linarith only [h, hs, hr]

end PseudoPrime.Analysis.ExponentialMeanSquare
