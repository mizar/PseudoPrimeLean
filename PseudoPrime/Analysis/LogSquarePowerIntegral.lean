/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PowerRiemannErrorIntegral
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Exact logarithmic-square moments of a negative power. -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For positive r and x, differentiate the explicit quadratic logarithmic primitive. -/
theorem log_sq_power_primitive_derivative {r x : ℝ} (hr : 0 < r) (hx : 0 < x) :
    HasDerivAt (fun t : ℝ ↦ -t ^ (-r) * ((Real.log t) ^ 2 / r + 2 * Real.log t / r ^ 2 + 2 / r ^ 3))
      ((Real.log x) ^ 2 * x ^ (-r - 1)) x := by
  have hp := (Real.hasDerivAt_rpow_const (p := -r) (Or.inl hx.ne')).neg
  have hl := Real.hasDerivAt_log hx.ne'
  have hpoly :=
    (((hl.pow 2).div_const r).add ((hl.const_mul 2).div_const (r ^ 2))).add_const (2 / r ^ 3)
  have h := hp.mul hpoly
  convert h using 1
  dsimp only [Pi.add_apply, Pi.neg_apply, Pi.pow_apply, Nat.reduceSub, pow_one, zero_add]
  rw [Real.rpow_sub_one hx.ne' (-r)]
  field_simp [hr.ne', hx.ne']
  ring

/-- For positive r, the quadratic logarithmic primitive tends to zero at infinity. -/
theorem log_sq_power_primitive_tendsto {r : ℝ} (hr : 0 < r) :
    Filter.Tendsto
      (fun t : ℝ ↦ -t ^ (-r) * ((Real.log t) ^ 2 / r + 2 * Real.log t / r ^ 2 + 2 / r ^ 3))
      Filter.atTop (nhds 0) := by
  have h2 : Filter.Tendsto (fun t : ℝ ↦ (Real.log t) ^ 2 / t ^ r) Filter.atTop (nhds 0) := by
    simpa only [Real.rpow_natCast] using
      (isLittleO_log_rpow_rpow_atTop ((2 : ℕ) : ℝ) hr).tendsto_div_nhds_zero
  have h1 := (isLittleO_log_rpow_atTop hr).tendsto_div_nhds_zero
  have h0 := tendsto_rpow_neg_atTop hr
  have h :=
    ((h2.div_const r).add ((h1.const_mul 2).div_const (r ^ 2))).add (h0.const_mul (2 / r ^ 3))
  simp only [zero_div, mul_zero, zero_add] at h
  have he :
    (fun t : ℝ ↦
        -(Real.log t ^ 2 / t ^ r / r + 2 * (Real.log t / t ^ r) / r ^ 2 +
            2 / r ^ 3 * t ^ (-r))) =ᶠ[Filter.atTop]
      (fun t : ℝ ↦ -t ^ (-r) * ((Real.log t) ^ 2 / r + 2 * Real.log t / r ^ 2 + 2 / r ^ 3)) := by
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
    rw [Real.rpow_neg ht]
    ring
  simpa only [neg_zero] using (h.neg).congr' he

/-- For positive r and a, the logarithmic-square power is integrable above a. -/
theorem log_sq_power_integrable {r a : ℝ} (hr : 0 < r) (ha : 0 < a) :
    MeasureTheory.IntegrableOn (fun t : ℝ ↦ (Real.log t) ^ 2 * t ^ (-r - 1)) (Set.Ioi a) := by
  exact
    MeasureTheory.integrableOn_Ioi_deriv_of_nonneg'
      (fun x hx ↦ log_sq_power_primitive_derivative hr (ha.trans_le hx))
      (fun x hx ↦ mul_nonneg (sq_nonneg (Real.log x)) (Real.rpow_nonneg (ha.trans hx).le _))
      (log_sq_power_primitive_tendsto hr)

/-- Evaluate the logarithmic-square power integral above a positive cutoff. -/
theorem log_sq_power_integral {r a : ℝ} (hr : 0 < r) (ha : 0 < a) :
    (∫ t in Set.Ioi a, (Real.log t) ^ 2 * t ^ (-r - 1)) =
      a ^ (-r) * ((Real.log a) ^ 2 / r + 2 * Real.log a / r ^ 2 + 2 / r ^ 3) := by
  have h :=
    MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto'
      (fun x hx ↦ log_sq_power_primitive_derivative hr (ha.trans_le hx))
      (log_sq_power_integrable hr ha) (log_sq_power_primitive_tendsto hr)
  simp only [zero_sub, neg_mul, neg_neg] at h
  exact h

end PseudoPrime.Analysis
