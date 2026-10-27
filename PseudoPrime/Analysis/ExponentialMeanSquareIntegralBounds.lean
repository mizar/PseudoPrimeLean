/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ExponentialMeanSquareIntervals
public import PseudoPrime.Analysis.MeanSquareCauchySchwarz

/-!
# Integrated exponential sums from mean squares

Cauchy--Schwarz on a positive multiplicative interval yields the integrated
zero-sum estimate without a pair-correlation hypothesis.
-/

@[expose] public section

namespace PseudoPrime.Analysis.ExponentialMeanSquare

/-- For positive input, the squared norm of the real inverse square root is the reciprocal.
Use positivity and the square-root square identity in interval Cauchy--Schwarz. -/
theorem norm_inv_sqrt_sq {y : ℝ} (hy : 0 < y) : ‖((Real.sqrt y)⁻¹ : ℝ) • (1 : ℂ)‖ ^ 2 = y⁻¹ := by
  rw [norm_smul, norm_one, mul_one, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg y)), inv_pow, Real.sq_sqrt hy.le]

/-- The real inverse-square-root scalar, viewed in the complex numbers, is continuous on any
closed interval with positive left endpoint. Invert the nonzero continuous square root. -/
theorem continuousOn_inv_sqrt {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun y : ℝ ↦ ((Real.sqrt y)⁻¹ : ℝ) • (1 : ℂ)) (Set.Icc a b) := by
  exact
    (Real.continuous_sqrt.continuousOn.inv₀
          (fun y hy ↦ Real.sqrt_ne_zero'.mpr (lt_of_lt_of_le ha hy.1))).smul
      continuousOn_const

/-- For x > 0 and c ≥ 1, the squared inverse-square-root norm integrates to log c.
Replace the integrand by the reciprocal and evaluate its positive-interval integral. -/
theorem interval_norm_inv_sqrt_sq {x c : ℝ} (hx : 0 < x) (hc : 1 ≤ c) :
    (∫ y : ℝ in x..c * x, ‖((Real.sqrt y)⁻¹ : ℝ) • (1 : ℂ)‖ ^ 2) = Real.log c := by
  have hxc : x ≤ c * x := by nlinarith only [hx, hc]
  calc
    _ = ∫ y : ℝ in x..c * x, y⁻¹ :=
      intervalIntegral.integral_congr
        (fun y hy ↦ norm_inv_sqrt_sq (lt_of_lt_of_le hx ((Set.uIcc_of_le hxc) ▸ hy).1))
    _ = Real.log c := by
      rw [integral_inv_of_pos hx (mul_pos (lt_of_lt_of_le zero_lt_one hc) hx),
        mul_div_cancel_right₀ _ hx.ne']

/-- For continuous f with integrable weighted square, x > 0 and c ≥ 1, the squared norm
of its inverse-square-root weighted logarithmic integral is at most x c cubed log c times
its energy. Apply actual interval Cauchy--Schwarz and the multiplicative interval bound. -/
theorem norm_integrated_logarithmic_sq_le {f : ℝ → ℂ} (hf : Continuous f)
    (hi : MeasureTheory.Integrable (fun v ↦ ‖f v‖ ^ 2 * weight v)) {x c : ℝ} (hx : 0 < x)
    (hc : 1 ≤ c) :
    ‖∫ y : ℝ in x..c * x, f (Real.log (y / x)) * (((Real.sqrt y)⁻¹ : ℝ) • (1 : ℂ))‖ ^ 2 ≤
      x * c ^ 3 * (Real.log c) * energy f := by
  have hxc : x ≤ c * x := by nlinarith only [hx, hc]
  have hlog : ContinuousOn (fun y : ℝ ↦ Real.log (y / x)) (Set.Icc x (c * x)) :=
    (continuous_id.div_const x).continuousOn.log
      (fun y hy ↦ div_ne_zero (ne_of_gt (lt_of_lt_of_le hx hy.1)) hx.ne')
  have h :=
    norm_intervalIntegral_mul_sq_le hxc (hf.comp_continuousOn hlog) (continuousOn_inv_sqrt hx)
  rw [interval_norm_inv_sqrt_sq hx hc] at h
  have hi' :=
    mul_le_mul_of_nonneg_right (multiplicative_interval_energy_le hf hi hx hc) (Real.log_nonneg hc)
  calc
    _ ≤ (∫ y : ℝ in x..c * x, ‖f (Real.log (y / x))‖ ^ 2) * Real.log c := h
    _ ≤ _ := by nlinarith only [hi']

/-- The integrated finite exponential sum satisfies the explicit energy bound on every
positive multiplicative interval. Supply its proved continuity and weighted integrability. -/
theorem exponentialSum_integrated_sq_le {ι : Type*} (s : Finset ι) (γ : ι → ℝ) (a : ι → ℂ) {x c : ℝ}
    (hx : 0 < x) (hc : 1 ≤ c) :
    ‖∫ y : ℝ in x..c * x,
            exponentialSum s γ a (Real.log (y / x)) * (((Real.sqrt y)⁻¹ : ℝ) • (1 : ℂ))‖ ^
        2 ≤
      x * c ^ 3 * (Real.log c) * energy (exponentialSum s γ a) := by
  exact
    norm_integrated_logarithmic_sq_le (continuous_exponentialSum s γ a)
      (integrable_energy_exponentialSum s γ a) hx hc

end PseudoPrime.Analysis.ExponentialMeanSquare
