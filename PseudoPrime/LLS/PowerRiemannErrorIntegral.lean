/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PowerLogTailConvergence

/-! # Explicit power-density integrals for the sharp RH Mangoldt error -/

@[expose] public section

namespace PseudoPrime.LLS

/-- The constant power variation density is integrable beyond a positive
cutoff for sigma greater than one. Use real-power tail integrability. -/
theorem power_constant_density_integrable {σ a : ℝ} (hσ : 1 < σ) (ha : 0 < a) :
    MeasureTheory.IntegrableOn (fun t : ℝ ↦ σ ^ 2 * t ^ (-σ - 1)) (Set.Ioi a) := by
  exact (integrableOn_Ioi_rpow_of_lt (by linarith only [hσ] : -σ - 1 < -1) ha).const_mul (σ ^ 2)

/-- The constant power variation density integrates to sigma times a to
the minus sigma. Apply the exact power integral and cancel nonzero sigma.
This is the constant term in the RH error budget. -/
theorem power_constant_density_integral_eq {σ a : ℝ} (hσ : 1 < σ) (ha : 0 < a) :
    (∫ t in Set.Ioi a, σ ^ 2 * t ^ (-σ - 1)) = σ * a ^ (-σ) := by
  rw [MeasureTheory.integral_const_mul,
    integral_Ioi_rpow_of_lt (by linarith only [hσ] : -σ - 1 < -1) ha, show -σ - 1 + 1 = -σ by ring,
    div_neg, neg_div, neg_neg]
  calc
    _ = (σ * a ^ (-σ)) * (σ / σ) := by ring
    _ = _ := by rw [div_self (zero_lt_one.trans hσ).ne', mul_one]

/-- At a positive input, multiply the power variation by the square root
by combining its two real exponents. This gives the exact tail exponent. -/
theorem power_sqrt_density_eq {σ t : ℝ} (ht : 0 < t) :
    Real.sqrt t * (σ ^ 2 * t ^ (-σ - 1)) = σ ^ 2 * t ^ (-σ - 1 / 2) := by
  rw [Real.sqrt_eq_rpow]
  calc
    _ = σ ^ 2 * (t ^ (1 / 2 : ℝ) * t ^ (-σ - 1)) := by ring
    _ = σ ^ 2 * t ^ ((1 / 2 : ℝ) + (-σ - 1)) := by rw [← Real.rpow_add ht]
    _ = _ := by
      congr 1; congr 1; ring

/-- The square-root power variation density is integrable beyond a
positive cutoff for sigma greater than one. Its combined exponent is
minus sigma minus one half, strictly less than minus one. -/
theorem power_sqrt_density_integrable {σ a : ℝ} (hσ : 1 < σ) (ha : 0 < a) :
    MeasureTheory.IntegrableOn (fun t : ℝ ↦ Real.sqrt t * (σ ^ 2 * t ^ (-σ - 1))) (Set.Ioi a) := by
  have h :=
    (integrableOn_Ioi_rpow_of_lt (by linarith only [hσ] : -σ - 1 / 2 < -1) ha).const_mul (σ ^ 2)
  apply MeasureTheory.IntegrableOn.congr_fun h _ measurableSet_Ioi
  intro t ht
  dsimp only
  exact (power_sqrt_density_eq (ha.trans ht)).symm

/-- The square-root power variation density has the exact improper
integral sigma squared times a to the one half minus sigma divided by
sigma minus one half. This supplies the sharp RH square-root error. -/
theorem power_sqrt_density_integral_eq {σ a : ℝ} (hσ : 1 < σ) (ha : 0 < a) :
    (∫ t in Set.Ioi a, Real.sqrt t * (σ ^ 2 * t ^ (-σ - 1))) =
      σ ^ 2 * a ^ (1 / 2 - σ) / (σ - 1 / 2) := by
  have he :
    (fun t : ℝ ↦ Real.sqrt t * (σ ^ 2 * t ^ (-σ - 1))) =ᵐ[MeasureTheory.volume.restrict (Set.Ioi a)]
      (fun t : ℝ ↦ σ ^ 2 * t ^ (-σ - 1 / 2)) :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi
      (fun t ht ↦ power_sqrt_density_eq (ha.trans ht))
  rw [MeasureTheory.integral_congr_ae he, MeasureTheory.integral_const_mul,
    integral_Ioi_rpow_of_lt (by linarith only [hσ] : -σ - 1 / 2 < -1) ha]
  rw [show -σ - 1 / 2 + 1 = 1 / 2 - σ by ring, show 1 / 2 - σ = -(σ - 1 / 2) by ring, div_neg,
    neg_div, neg_neg]
  ring

/-- For nonnegative sigma and input at least one, bound the logarithmic
power boundary by one plus sigma times the decaying power t to the one
minus sigma. Log t is at most t and the constant is at most t. -/
theorem power_log_boundary_le_majorant {σ t : ℝ} (hσ : 0 ≤ σ) (ht : 1 ≤ t) :
    t ^ (-σ) * (1 + σ * Real.log t) ≤ (1 + σ) * t ^ (1 - σ) := by
  have hh := mul_le_mul_of_nonneg_left (Real.log_le_self (zero_le_one.trans ht)) hσ
  have hm :=
    mul_le_mul_of_nonneg_left (show 1 + σ * Real.log t ≤ (1 + σ) * t by linarith only [hh, ht])
      (Real.rpow_nonneg (zero_le_one.trans ht) (-σ))
  rw [show 1 - σ = -σ + 1 by ring, Real.rpow_add_one (zero_lt_one.trans_le ht).ne' (-σ)]
  convert hm using 1
  ring

/-- For sigma greater than one, the logarithmic power boundary vanishes
at infinity. Sandwich it between zero and the proved power majorant.
This justifies the upper endpoint of the logarithmic error integral. -/
theorem tendsto_power_log_boundary_zero {σ : ℝ} (hσ : 1 < σ) :
    Filter.Tendsto (fun t : ℝ ↦ t ^ (-σ) * (1 + σ * Real.log t)) Filter.atTop (nhds (0 : ℝ)) := by
  have hr : Filter.Tendsto (fun t : ℝ ↦ t ^ (1 - σ)) Filter.atTop (nhds (0 : ℝ)) := by
    rw [show 1 - σ = -(σ - 1) by ring]
    exact tendsto_rpow_neg_atTop (sub_pos.mpr hσ)
  have hm := hr.const_mul (1 + σ)
  simp only [mul_zero] at hm
  apply Filter.Tendsto.squeeze' tendsto_const_nhds hm
  · exact
      (Filter.eventually_ge_atTop (1 : ℝ)).mono
        (fun t ht ↦
          mul_nonneg (Real.rpow_nonneg (zero_le_one.trans ht) (-σ))
            (add_nonneg zero_le_one (mul_nonneg (zero_lt_one.trans hσ).le (Real.log_nonneg ht))))
  · exact
      (Filter.eventually_ge_atTop (1 : ℝ)).mono
        (fun t ht ↦ power_log_boundary_le_majorant (zero_lt_one.trans hσ).le ht)

/-- Beyond a cutoff at least one, the logarithmic power variation is
integrable for sigma greater than one. Dominate its nonnegative integrand
by the already integrable linear density using log t at most t. -/
theorem power_log_density_integrable {σ a : ℝ} (hσ : 1 < σ) (ha : 1 ≤ a) :
    MeasureTheory.IntegrableOn (fun t : ℝ ↦ Real.log t * (σ ^ 2 * t ^ (-σ - 1))) (Set.Ioi a) := by
  have hl : ContinuousOn Real.log (Set.Ioi a) := fun t ht ↦
    (Real.hasDerivAt_log
        (zero_lt_one.trans_le (ha.trans ht.le)).ne').continuousAt.continuousWithinAt
  have hc : ContinuousOn (fun t : ℝ ↦ Real.log t * (σ ^ 2 * t ^ (-σ - 1))) (Set.Ioi a) :=
    hl.mul
      (continuousOn_const.mul
        (fun t ht ↦
          (Real.continuousAt_rpow_const t (-σ - 1)
              (Or.inl (zero_lt_one.trans_le (ha.trans ht.le)).ne')).continuousWithinAt))
  refine
    (power_linear_density_integrable hσ (zero_lt_one.trans_le ha)).mono'
      (hc.aestronglyMeasurable measurableSet_Ioi) ?_
  apply MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi
  intro t ht
  have ht1 := ha.trans ht.le
  have hq := mul_nonneg (sq_nonneg σ) (Real.rpow_nonneg (zero_le_one.trans ht1) (-σ - 1))
  rw [Real.norm_of_nonneg (mul_nonneg (Real.log_nonneg ht1) hq)]
  exact mul_le_mul_of_nonneg_right (Real.log_le_self (zero_le_one.trans ht1)) hq

/-- The logarithmic power variation has exact improper integral
 a to the minus sigma times one plus sigma log a. Use the finite log
kernel formula, integrability and the vanishing logarithmic boundary. -/
theorem power_log_density_integral_eq {σ a : ℝ} (hσ : 1 < σ) (ha : 1 ≤ a) :
    (∫ t in Set.Ioi a, Real.log t * (σ ^ 2 * t ^ (-σ - 1))) = a ^ (-σ) * (1 + σ * Real.log a) := by
  have hi :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi a (power_log_density_integrable hσ ha)
      (Filter.tendsto_id : Filter.Tendsto (fun t : ℝ ↦ t) Filter.atTop Filter.atTop)
  have hl :=
    (tendsto_const_nhds :
          Filter.Tendsto (fun _ : ℝ ↦ a ^ (-σ) * (1 + σ * Real.log a)) Filter.atTop
            (nhds (a ^ (-σ) * (1 + σ * Real.log a)))).sub
      (tendsto_power_log_boundary_zero hσ)
  simp only [sub_zero] at hl
  have he :
    (fun b : ℝ ↦ ∫ t in a..b, Real.log t * (σ ^ 2 * t ^ (-σ - 1))) =ᶠ[Filter.atTop]
      (fun b : ℝ ↦ a ^ (-σ) * (1 + σ * Real.log a) - b ^ (-σ) * (1 + σ * Real.log b)) := by
    apply (Filter.eventually_ge_atTop a).mono
    intro b hb
    simpa only [div_one] using
      Analysis.power_log_integral_eq σ (by norm_num only : (0 : ℝ) < 1) (zero_lt_one.trans_le ha) hb
  exact tendsto_nhds_unique hi (hl.congr' he.symm)

/-- The explicit envelope for the logarithmic Mangoldt error under RH.
At inputs at least one it is sqrt t over twenty, plus 1839/1000 log t,
plus 21/20. It is integrated against each nonnegative scalar power density. -/
noncomputable def powerRiemannErrorEnvelope (t : ℝ) : ℝ :=
  Real.sqrt t / 20 + (1839 / 1000 : ℝ) * Real.log t + (21 / 20 : ℝ)

/-- The exact integrated RH envelope for exponent sigma and cutoff a.
It combines the proved square-root, logarithmic and constant power-density
integrals. The error-bound theorem assumes sigma greater than one and a at least one. -/
noncomputable def powerRiemannErrorBudget (σ a : ℝ) : ℝ :=
  (1 / 20 : ℝ) * (σ ^ 2 * a ^ (1 / 2 - σ) / (σ - 1 / 2)) +
    (1839 / 1000 : ℝ) * (a ^ (-σ) * (1 + σ * Real.log a)) +
    (21 / 20 : ℝ) * (σ * a ^ (-σ))

/-- Beyond a cutoff at least one, the full RH envelope times the scalar
power variation density is integrable when sigma exceeds one. Combine the
three independently integrable error components with their explicit constants. -/
theorem powerRiemannErrorEnvelope_density_integrable {σ a : ℝ} (hσ : 1 < σ) (ha : 1 ≤ a) :
    MeasureTheory.IntegrableOn (fun t : ℝ ↦ powerRiemannErrorEnvelope t * (σ ^ 2 * t ^ (-σ - 1)))
      (Set.Ioi a) := by
  have hs := (power_sqrt_density_integrable hσ (zero_lt_one.trans_le ha)).const_mul (1 / 20 : ℝ)
  have hl := (power_log_density_integrable hσ ha).const_mul (1839 / 1000 : ℝ)
  have hc :=
    (power_constant_density_integrable hσ (zero_lt_one.trans_le ha)).const_mul (21 / 20 : ℝ)
  apply ((hs.add hl).add hc).congr
  apply Filter.Eventually.of_forall
  intro t
  dsimp only [Pi.add_apply, powerRiemannErrorEnvelope]
  ring

/-- The integral of the full RH envelope is exactly the explicit scalar
error budget. Integrate the three components using proved integrability
and their exact improper integral formulas. -/
theorem powerRiemannErrorEnvelope_density_integral_eq {σ a : ℝ} (hσ : 1 < σ) (ha : 1 ≤ a) :
    (∫ t in Set.Ioi a, powerRiemannErrorEnvelope t * (σ ^ 2 * t ^ (-σ - 1))) =
      powerRiemannErrorBudget σ a := by
  have hs := (power_sqrt_density_integrable hσ (zero_lt_one.trans_le ha)).const_mul (1 / 20 : ℝ)
  have hl := (power_log_density_integrable hσ ha).const_mul (1839 / 1000 : ℝ)
  have hc :=
    (power_constant_density_integrable hσ (zero_lt_one.trans_le ha)).const_mul (21 / 20 : ℝ)
  have he :
    (fun t : ℝ ↦ powerRiemannErrorEnvelope t * (σ ^ 2 * t ^ (-σ - 1))) =
      (fun t : ℝ ↦
        ((1 / 20 : ℝ) * (Real.sqrt t * (σ ^ 2 * t ^ (-σ - 1))) +
            (1839 / 1000 : ℝ) * (Real.log t * (σ ^ 2 * t ^ (-σ - 1)))) +
          (21 / 20 : ℝ) * (σ ^ 2 * t ^ (-σ - 1))) := by
    funext t
    dsimp only [powerRiemannErrorEnvelope]
    ring
  rw [he, MeasureTheory.integral_add (hs.fun_add hl) hc, MeasureTheory.integral_add hs hl]
  simp only [MeasureTheory.integral_const_mul,
    power_sqrt_density_integral_eq hσ (zero_lt_one.trans_le ha),
    power_log_density_integral_eq hσ ha,
    power_constant_density_integral_eq hσ (zero_lt_one.trans_le ha)]
  rfl

/-- Under RH, sigma greater than one and cutoff at least one, the actual
Mangoldt error times the scalar power variation is integrable. Subtract
the proved logarithmic and linear integrands, preserving the signed error. -/
theorem powerRiemannError_density_integrable (hRH : RiemannHypothesis) {σ a : ℝ} (hσ : 1 < σ)
    (ha : 1 ≤ a) :
    MeasureTheory.IntegrableOn
      (fun t : ℝ ↦
        (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t - t) * (σ ^ 2 * t ^ (-σ - 1)))
      (Set.Ioi a) := by
  have hs := integrableOn_power_logWeightedMangoldtSum hRH hσ ha
  have ht := power_linear_density_integrable hσ (zero_lt_one.trans_le ha)
  apply (hs.sub ht).congr
  apply Filter.Eventually.of_forall
  intro t
  dsimp only [Pi.sub_apply]
  ring

/-- Under RH, sigma greater than one and cutoff at least one, the actual
scalar error integral has absolute value at most its explicit budget.
Apply the sharp Mangoldt error envelope pointwise, then use integral
monotonicity and the exact three-component integral. -/
theorem powerRiemannError_integral_abs_le (hRH : RiemannHypothesis) {σ a : ℝ} (hσ : 1 < σ)
    (ha : 1 ≤ a) :
    |∫ t in Set.Ioi a,
          (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t - t) * (σ ^ 2 * t ^ (-σ - 1))| ≤
      powerRiemannErrorBudget σ a := by
  have hs := powerRiemannError_density_integrable hRH hσ ha
  have he := powerRiemannErrorEnvelope_density_integrable hσ ha
  have hb :
    ∀ᵐ t : ℝ ∂MeasureTheory.volume.restrict (Set.Ioi a),
      ‖(AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t - t) * (σ ^ 2 * t ^ (-σ - 1))‖ ≤
        powerRiemannErrorEnvelope t * (σ ^ 2 * t ^ (-σ - 1)) := by
    apply MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi
    intro t ht
    have ht1 := ha.trans ht.le
    have hq := mul_nonneg (sq_nonneg σ) (Real.rpow_nonneg (zero_le_one.trans ht1) (-σ - 1))
    have hr := logWeightedMangoldtSum_error_le_refined_global hRH (zero_lt_one.trans_le ht1)
    rw [max_eq_right ht1] at hr
    rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg hq]
    exact mul_le_mul_of_nonneg_right hr hq
  have hm :=
    (MeasureTheory.norm_integral_le_integral_norm
          (fun t : ℝ ↦
            (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t - t) *
              (σ ^ 2 * t ^ (-σ - 1)))).trans
      (MeasureTheory.integral_mono_ae hs.norm he hb)
  simpa only [Real.norm_eq_abs, powerRiemannErrorEnvelope_density_integral_eq hσ ha] using hm

end PseudoPrime.LLS
