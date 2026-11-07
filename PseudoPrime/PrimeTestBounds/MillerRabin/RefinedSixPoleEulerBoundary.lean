/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleEulerIntegrable
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Boundary decay for the refined six-pole Euler tail. -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A negative power dominates every fixed power of the logarithm at infinity. -/
theorem refined_scaled_log_power_tendsto (n : ℕ) :
    Filter.Tendsto (fun x : ℝ ↦ x ^ (-(29 / 50 : ℝ)) * (Real.log x) ^ n) Filter.atTop (nhds 0) := by
  have h :
    Filter.Tendsto (fun x : ℝ ↦ (Real.log x) ^ n / x ^ (29 / 50 : ℝ)) Filter.atTop (nhds 0) := by
    simpa only [Real.rpow_natCast] using
      (isLittleO_log_rpow_rpow_atTop (n : ℝ)
          (by norm_num only : (0 : ℝ) < 29 / 50)).tendsto_div_nhds_zero
  apply h.congr'
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
  rw [Real.rpow_neg hx.le, div_eq_mul_inv, mul_comm]

/-- The Euler weight multiplied by its argument tends to zero at infinity. -/
theorem refined_weight_times_self_tendsto :
    Filter.Tendsto (fun x : ℝ ↦ x * refinedEulerRealWeight x) Filter.atTop (nhds 0) := by
  have h0 := (refined_scaled_log_power_tendsto 0).const_mul (3 : ℝ)
  have h1 := (refined_scaled_log_power_tendsto 1).const_mul (81 / 25 : ℝ)
  have h2 := (refined_scaled_log_power_tendsto 2).const_mul (729 / 625 : ℝ)
  have h := ((h0.add h1).add h2).div_const 8
  simp only [mul_zero, zero_add, zero_div] at h
  apply h.congr'
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
  have he : x ^ (-(29 / 50 : ℝ)) = x ^ (-(79 / 50 : ℝ)) * x := by
    rw [show (-(29 / 50 : ℝ)) = -(79 / 50 : ℝ) + 1 by norm_num only, Real.rpow_add_one hx.ne']
  unfold refinedEulerRealWeight
  simp only [pow_zero, pow_one]
  rw [he]
  ring

/-- The logarithmic slope multiplied by its argument tends to zero at infinity. -/
theorem refined_slope_times_self_tendsto :
    Filter.Tendsto (fun x : ℝ ↦ x * refinedEulerSlope x) Filter.atTop (nhds 0) := by
  have h0 := (refined_scaled_log_power_tendsto 0).const_mul (-(3 / 2 : ℝ))
  have h1 := (refined_scaled_log_power_tendsto 1).const_mul (-(3483 / 1250 : ℝ))
  have h2 := (refined_scaled_log_power_tendsto 2).const_mul (-(57591 / 31250 : ℝ))
  have h := ((h0.add h1).add h2).div_const 8
  simp only [mul_zero, zero_add, zero_div] at h
  apply h.congr'
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
  have he : x ^ (-(29 / 50 : ℝ)) = x ^ (-(79 / 50 : ℝ)) * x := by
    rw [show (-(29 / 50 : ℝ)) = -(79 / 50 : ℝ) + 1 by norm_num only, Real.rpow_add_one hx.ne']
  unfold refinedEulerSlope
  simp only [pow_zero, pow_one]
  rw [he]
  ring

/-- Under RH, the upper boundary term in the Euler tail formula tends to zero. -/
theorem refined_euler_boundary_tendsto (hRH : RiemannHypothesis) :
    Filter.Tendsto
      (fun t : ℝ ↦
        refinedEulerSlope t * AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t -
          refinedEulerRealWeight t * Chebyshev.psi t)
      Filter.atTop (nhds 0) := by
  have hS0 :
    ∀ᶠ t : ℝ in Filter.atTop,
      (0 : ℝ) ≤ AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t / t := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with t ht
    exact
      div_nonneg (LLS.logWeightedMangoldtSum_nonneg_of_pos (zero_lt_one.trans_le ht))
        (zero_le_one.trans ht)
  have hS4 :
    ∀ᶠ t : ℝ in Filter.atTop, AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t / t ≤ 4 := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with t ht
    apply (div_le_iff₀ (zero_lt_one.trans_le ht)).mpr
    linarith only [LLS.logWeightedMangoldtSum_le_four_mul hRH ht]
  have hP0 : ∀ᶠ t : ℝ in Filter.atTop, (0 : ℝ) ≤ Chebyshev.psi t / t := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with t ht
    exact div_nonneg (Chebyshev.psi_nonneg t) (zero_le_one.trans ht)
  have hP4 : ∀ᶠ t : ℝ in Filter.atTop, Chebyshev.psi t / t ≤ Real.log 4 + 4 := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with t ht
    apply (div_le_iff₀ (zero_lt_one.trans_le ht)).mpr
    exact Chebyshev.psi_le_const_mul_self (zero_le_one.trans ht)
  have hs := bdd_le_mul_tendsto_zero hS0 hS4 refined_slope_times_self_tendsto
  have hp := bdd_le_mul_tendsto_zero hP0 hP4 refined_weight_times_self_tendsto
  have hs' :
    Filter.Tendsto
      (fun t : ℝ ↦ refinedEulerSlope t * AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t)
      Filter.atTop (nhds 0) := by
    apply hs.congr'
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
    field_simp [ht.ne']
  have hp' :
    Filter.Tendsto (fun t : ℝ ↦ refinedEulerRealWeight t * Chebyshev.psi t) Filter.atTop
      (nhds 0) := by
    apply hp.congr'
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
    field_simp [ht.ne']
  simpa only [sub_zero] using hs'.sub hp'

end PseudoPrime.PrimeTestBounds.MillerRabin
