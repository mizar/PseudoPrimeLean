/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleEulerSmoothed
public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleEulerSqrtIntegral

/-! Certified universal Euler sum bound for the refined six-pole kernel. -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Kernel reduction checks the rational power intervals.
/-- Check rational intervals for the three negative powers occurring at 1000. -/
theorem refined_power_1000_checks :
    AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 1000 (18197 / 1000000)
          (18198 / 1000000) 29 50 =
        true ∧
      AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 1000 (575 / 1000000)
          (576 / 1000000) 27 25 =
        true ∧
      AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 1000 (181 / 10000000)
          (182 / 10000000) 79 50 =
        true := by
  decide +kernel

/-- An upper rational bound for the logarithm of 1000. -/
theorem refined_log_1000_upper : Real.log 1000 ≤ (6907756 / 1000000 : ℝ) := by
  have h := Analysis.rationalLogIntervalCheck_sound refined_log_1000_check
  norm_num only at h ⊢
  exact h.2

/-- The three negative powers at 1000 lie in their certified rational intervals. -/
theorem refined_power_1000_bounds :
    (18197 / 1000000 : ℝ) ≤ (1000 : ℝ) ^ (-(29 / 50 : ℝ)) ∧
      (1000 : ℝ) ^ (-(29 / 50 : ℝ)) ≤ 18198 / 1000000 ∧
      (575 / 1000000 : ℝ) ≤ (1000 : ℝ) ^ (-(27 / 25 : ℝ)) ∧
      (1000 : ℝ) ^ (-(27 / 25 : ℝ)) ≤ 576 / 1000000 ∧
      (181 / 10000000 : ℝ) ≤ (1000 : ℝ) ^ (-(79 / 50 : ℝ)) ∧
      (1000 : ℝ) ^ (-(79 / 50 : ℝ)) ≤ 182 / 10000000 := by
  have h1 :=
    AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound refined_power_1000_checks.1
  have h2 :=
    AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound refined_power_1000_checks.2.1
  have h3 :=
    AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound refined_power_1000_checks.2.2
  norm_num only at h1 h2 h3 ⊢
  exact ⟨h1.1, h1.2, h2.1, h2.2, h3.1, h3.2⟩

/-- Certified upper and lower rational bounds for the weight and its slope at 1000. -/
theorem refined_weight_slope_1000_bounds :
    0 ≤ refinedEulerRealWeight 1000 ∧
      refinedEulerRealWeight 1000 ≤ (187 / 1000000 : ℝ) ∧
      -(251 / 1000000 : ℝ) ≤ refinedEulerSlope 1000 ∧ refinedEulerSlope 1000 ≤ 0 := by
  have hl := refined_log_1000_lower
  have hu := refined_log_1000_upper
  have hv0 : 0 ≤ (1000 : ℝ) ^ (-(79 / 50 : ℝ)) := Real.rpow_nonneg (by norm_num only) _
  have hv := refined_power_1000_bounds.2.2.2.2.2
  have hq0 : 0 ≤ 3 + (81 / 25 : ℝ) * Real.log 1000 + (729 / 625 : ℝ) * (Real.log 1000) ^ 2 := by
    nlinarith only [hl, sq_nonneg (Real.log 1000)]
  have hq : 3 + (81 / 25 : ℝ) * Real.log 1000 + (729 / 625 : ℝ) * (Real.log 1000) ^ 2 ≤ 82 := by
    nlinarith only [hl, hu, sq_nonneg (Real.log 1000 - (6907756 / 1000000 : ℝ))]
  have hd0 :
    (81 / 25 : ℝ) + (1458 / 625 : ℝ) * Real.log 1000 -
        (79 / 50 : ℝ) *
          (3 + (81 / 25 : ℝ) * Real.log 1000 + (729 / 625 : ℝ) * (Real.log 1000) ^ 2) ≤
      0 := by
    nlinarith only [hl, hu, sq_nonneg (Real.log 1000)]
  have hd :
    -(110 : ℝ) ≤
      (81 / 25 : ℝ) + (1458 / 625 : ℝ) * Real.log 1000 -
        (79 / 50 : ℝ) *
          (3 + (81 / 25 : ℝ) * Real.log 1000 + (729 / 625 : ℝ) * (Real.log 1000) ^ 2) := by
    nlinarith only [hl, hu, sq_nonneg (Real.log 1000 - (6907756 / 1000000 : ℝ))]
  have hwu := mul_le_mul hv hq hq0 (by norm_num only : (0 : ℝ) ≤ 182 / 10000000)
  have hdl := mul_le_mul_of_nonneg_left hd hv0
  have hdm := mul_le_mul_of_nonpos_right hv (by norm_num only : (-(110 : ℝ)) ≤ 0)
  unfold refinedEulerRealWeight refinedEulerSlope
  constructor
  · exact div_nonneg (mul_nonneg hv0 hq0) (by norm_num only)
  constructor
  · nlinarith only [hwu]
  constructor
  · nlinarith only [hdl, hdm]
  · exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hv0 hd0) (by norm_num only)

/-- Bound the two Euler boundary corrections at cutoff 1000 by 41/10000. -/
theorem refined_boundary_1000_upper :
    refinedEulerRealWeight 1000 * (1000 - Chebyshev.psi 1000) +
        refinedEulerSlope 1000 *
          (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum 1000 - 1000) ≤
      (41 / 10000 : ℝ) := by
  obtain ⟨hw0, hw, hd, hd0⟩ := refined_weight_slope_1000_bounds
  have hp := refined_psi_1000_lower
  have hs := refined_smooth_1000_lower
  have ha :=
    mul_le_mul_of_nonneg_left (show 1000 - Chebyshev.psi 1000 ≤ (83 / 25 : ℝ) by linarith only [hp])
      hw0
  have hb := mul_le_mul_of_nonneg_right hw (by norm_num only : (0 : ℝ) ≤ 83 / 25)
  have hc :=
    mul_le_mul_of_nonpos_left
      (show -(341 / 25 : ℝ) ≤ AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum 1000 - 1000 by
        linarith only [hs])
      hd0
  have he := mul_le_mul_of_nonpos_right hd (by norm_num only : (-(341 / 25 : ℝ)) ≤ 0)
  nlinarith only [ha, hb, hc, he]

/-- The two explicit improper-integral contributions at 1000 sum to at most 479/1000. -/
theorem refined_integral_1000_upper :
    (∫ t in Set.Ioi (1000 : ℝ), refinedEulerRealWeight t) +
        (1 / 20 : ℝ) * (∫ t in Set.Ioi (1000 : ℝ), Real.sqrt t * refinedEulerVariation t) ≤
      (479 / 1000 : ℝ) := by
  rw [refined_weight_integral_eq (by norm_num only : (1 : ℝ) ≤ 1000),
    refined_sqrt_variation_integral_eq (by norm_num only : (1 : ℝ) ≤ 1000)]
  have hu := refined_log_1000_upper
  have hlog0 : 0 ≤ Real.log 1000 := Real.log_nonneg (by norm_num only)
  have hsq := pow_le_pow_left₀ hlog0 hu 2
  have hp0 : 0 ≤ (1000 : ℝ) ^ (-(29 / 50 : ℝ)) := Real.rpow_nonneg (by norm_num only) _
  have hq0 : 0 ≤ (1000 : ℝ) ^ (-(27 / 25 : ℝ)) := Real.rpow_nonneg (by norm_num only) _
  have hp := refined_power_1000_bounds.2.1
  have hq := refined_power_1000_bounds.2.2.2.1
  have ha :
    (3 / (29 / 50 : ℝ) + (81 / 25 : ℝ) * (Real.log 1000 / (29 / 50 : ℝ) + 1 / (29 / 50 : ℝ) ^ 2) +
        (729 / 625 : ℝ) *
          ((Real.log 1000) ^ 2 / (29 / 50 : ℝ) + 2 * Real.log 1000 / (29 / 50 : ℝ) ^ 2 +
            2 / (29 / 50 : ℝ) ^ 3)) ≤
      210 := by
    norm_num only [div_eq_mul_inv] at hsq hu ⊢
    nlinarith only [hu, hsq]
  have hb :
    ((4549689 / 1562500 : ℝ) *
            ((Real.log 1000) ^ 2 / (27 / 25 : ℝ) + 2 * Real.log 1000 / (27 / 25 : ℝ) ^ 2 +
              2 / (27 / 25 : ℝ) ^ 3) +
          (44793 / 62500 : ℝ) * (Real.log 1000 / (27 / 25 : ℝ) + 1 / (27 / 25 : ℝ) ^ 2) -
        (1041 / 2500 : ℝ) / (27 / 25 : ℝ)) ≤
      174 := by
    norm_num only [div_eq_mul_inv] at hsq hu ⊢
    nlinarith only [hu, hsq]
  have hpa := mul_le_mul_of_nonneg_left ha hp0
  have hqb := mul_le_mul_of_nonneg_left hb hq0
  nlinarith only [hpa, hqb, hp, hq]

/-- Under RH, the universal refined Euler sum is strictly below the zero-mass threshold. -/
theorem refined_euler_total_upper (hRH : RiemannHypothesis) :
    (∑' m : ℕ, ArithmeticFunction.vonMangoldt m * refinedSixEulerWeight m) <
      (53 / 25 : ℝ) * (27 / 25 : ℝ) ^ 5 := by
  have h := refined_euler_upper_1000 hRH
  have hb := refined_boundary_1000_upper
  have hi := refined_integral_1000_upper
  norm_num only at h hb hi ⊢
  linarith only [h, hb, hi]

end PseudoPrime.PrimeTestBounds.MillerRabin
