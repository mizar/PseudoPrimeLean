/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleEulerUpper
public import PseudoPrime.Analysis.LogPowerTailIntegral
public import PseudoPrime.Analysis.LogPowerAsymptotics
public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleSharpError
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterEulerPrefix1000Sharp
public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleEulerPrefixUpper

/-! Integrability of the logarithmic error term in the refined Euler tail. -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The logarithm times the refined Euler variation is integrable beyond any cutoff at least
three. This makes the logarithmic term of the centered Euler error available for integration. -/
theorem refined_log_variation_integrable {a : ℝ} (ha : 3 ≤ a) :
    MeasureTheory.IntegrableOn (fun t : ℝ ↦ Real.log t * refinedEulerVariation t) (Set.Ioi a) := by
  have ha0 : 0 < a := by linarith only [ha]
  have hc : ContinuousOn (fun t : ℝ ↦ Real.log t * refinedEulerVariation t) (Set.Ioi a) := by
    apply ContinuousOn.mul
    · intro t ht
      exact (Real.continuousAt_log (ha0.trans ht).ne').continuousWithinAt
    · intro t ht
      have ht0 := ha0.trans ht
      unfold refinedEulerVariation
      exact
        (((Real.continuousAt_rpow_const t (-(79 / 50 : ℝ) - 1) (Or.inl ht0.ne')).mul
                (((continuousAt_const.mul ((Real.continuousAt_log ht0.ne').pow 2)).add
                      (continuousAt_const.mul (Real.continuousAt_log ht0.ne'))).sub
                  continuousAt_const)).div_const
            8).continuousWithinAt
  refine
    (refined_linear_variation_integrable ha).mono' (hc.aestronglyMeasurable measurableSet_Ioi) ?_
  apply MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi
  intro t ht
  have ht3 : (3 : ℝ) ≤ t := ha.trans ht.le
  have ht0 : 0 < t := ha0.trans ht
  have hv := refined_variation_nonneg ht3
  have hl : 0 ≤ Real.log t := Real.log_nonneg (by linarith only [ht3])
  rw [Real.norm_of_nonneg (mul_nonneg hl hv)]
  exact mul_le_mul_of_nonneg_right (by linarith only [Real.log_le_sub_one_of_pos ht0]) hv

/-- The refined Euler variation is integrable above every cutoff at least three. This supplies
the constant term of the centered Euler error. -/
theorem refined_variation_integrable {a : ℝ} (ha : 3 ≤ a) :
    MeasureTheory.IntegrableOn refinedEulerVariation (Set.Ioi a) := by
  have ha0 : 0 < a := by linarith only [ha]
  have hc : ContinuousOn refinedEulerVariation (Set.Ioi a) := by
    intro t ht
    have ht0 := ha0.trans ht
    unfold refinedEulerVariation
    exact
      (((Real.continuousAt_rpow_const t (-(79 / 50 : ℝ) - 1) (Or.inl ht0.ne')).mul
              (((continuousAt_const.mul ((Real.continuousAt_log ht0.ne').pow 2)).add
                    (continuousAt_const.mul (Real.continuousAt_log ht0.ne'))).sub
                continuousAt_const)).div_const
          8).continuousWithinAt
  refine
    (refined_linear_variation_integrable ha).mono' (hc.aestronglyMeasurable measurableSet_Ioi) ?_
  apply MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi
  intro t ht
  have ht3 : (3 : ℝ) ≤ t := ha.trans ht.le
  have hv := refined_variation_nonneg ht3
  rw [Real.norm_of_nonneg hv]
  nlinarith only [mul_nonneg (show 0 ≤ t - 1 by linarith only [ht3]) hv]

/-- Under RH, the centered Euler tail is bounded below by the square-root, logarithmic and
constant variation integrals. The estimate retains all three terms of the sharp Mangoldt error. -/
theorem refined_euler_centered_lower (hRH : RiemannHypothesis) {a : ℝ} (ha : 3 ≤ a) :
    (∑ n ∈ Finset.Ioc 0 ⌊a⌋₊, ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n) +
          refinedEulerRealWeight a * (a - Chebyshev.psi a) +
          refinedEulerSlope a * (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum a - a) +
          (∫ t in Set.Ioi a, refinedEulerRealWeight t) -
        (231 / 5000 : ℝ) * (∫ t in Set.Ioi a, Real.sqrt t * refinedEulerVariation t) -
        (1839 / 1000 : ℝ) * (∫ t in Set.Ioi a, Real.log t * refinedEulerVariation t) -
        2 * (∫ t in Set.Ioi a, refinedEulerVariation t) ≤
      ∑' n : ℕ, ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n := by
  have hi :=
    (refined_variation_mangoldt_integrable hRH ha).sub (refined_linear_variation_integrable ha)
  have he :
    (fun t : ℝ ↦
        (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t - t) * refinedEulerVariation t) =
      (fun t : ℝ ↦
        AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t * refinedEulerVariation t -
          t * refinedEulerVariation t) := by
    funext t
    ring
  have hi' :
    MeasureTheory.IntegrableOn
      (fun t : ℝ ↦
        (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t - t) * refinedEulerVariation t)
      (Set.Ioi a) := by
    rw [he]
    exact hi
  have hs := (refined_sqrt_variation_integrable ha).const_mul (231 / 5000 : ℝ)
  have hl := (refined_log_variation_integrable ha).const_mul (1839 / 1000 : ℝ)
  have hv := (refined_variation_integrable ha).const_mul (2 : ℝ)
  have hb :
    (∫ t in Set.Ioi a,
        -((231 / 5000 : ℝ) * (Real.sqrt t * refinedEulerVariation t) +
            (1839 / 1000 : ℝ) * (Real.log t * refinedEulerVariation t) +
            2 * refinedEulerVariation t)) ≤
      ∫ t in Set.Ioi a,
        (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t - t) *
          refinedEulerVariation t := by
    apply MeasureTheory.integral_mono_ae ((hs.add hl).add hv).neg hi'
    apply MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi
    intro t ht
    have ht3 : (3 : ℝ) ≤ t := ha.trans ht.le
    have ht0 : 0 < t := by linarith only [ht3]
    have ht1 : (1 : ℝ) ≤ t := by linarith only [ht3]
    have hm := refined_log_mangoldt_error hRH ht0
    rw [max_eq_right ht1] at hm
    have hn := (abs_le.mp hm).1
    have hv0 := refined_variation_nonneg ht3
    have h := mul_le_mul_of_nonneg_right hn hv0
    dsimp only [Pi.add_apply, Pi.neg_apply]
    nlinarith only [h]
  have hsum := MeasureTheory.integral_add (hs.add hl) hv
  have hsum' := MeasureTheory.integral_add hs hl
  simp only [Pi.add_apply] at hsum hsum'
  rw [MeasureTheory.integral_neg, hsum, hsum'] at hb
  simp only [MeasureTheory.integral_const_mul] at hb
  rw [refined_euler_centered_tail hRH ha]
  linarith only [hb]

set_option maxRecDepth 2000 in
-- Elaborating membership in the checked prefix requires more than the default recursion depth.
/-- At cutoff 1000, the checked Euler prefix gives a strict lower estimate for the centered
Euler total under RH. The remaining explicit terms are the endpoint corrections and tail errors. -/
theorem quarter_euler_centered_lower_1000 (hRH : RiemannHypothesis) :
    (178404 / 100000 : ℝ) * (27 / 25 : ℝ) ^ 5 +
          refinedEulerRealWeight 1000 * (1000 - Chebyshev.psi 1000) +
          refinedEulerSlope 1000 *
            (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum 1000 - 1000) +
          (∫ t in Set.Ioi (1000 : ℝ), refinedEulerRealWeight t) -
        (231 / 5000 : ℝ) * (∫ t in Set.Ioi (1000 : ℝ), Real.sqrt t * refinedEulerVariation t) -
        (1839 / 1000 : ℝ) * (∫ t in Set.Ioi (1000 : ℝ), Real.log t * refinedEulerVariation t) -
        2 * (∫ t in Set.Ioi (1000 : ℝ), refinedEulerVariation t) <
      ∑' n : ℕ, ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n := by
  have he :
    (∑ n ∈ Finset.Ioc 0 1000, ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n) =
      ∑ n ∈ refinedEulerPrefixSet, ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n := by
    symm
    apply Finset.sum_subset refined_euler_prefix_subset
    intro n hn hn'
    have hnp : ¬IsPrimePow n := fun hp ↦ hn' (refined_euler_prefix_support n hn hp)
    rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hnp, zero_mul]
  have h := refined_euler_centered_lower hRH (a := (1000 : ℝ)) (by norm_num only)
  norm_num only [Nat.floor_ofNat] at h
  rw [he] at h
  linarith only [h, quarter_euler_prefix1000_sharp]

/-- At a cutoff at least three, the integral of the Euler variation is the negative boundary
slope. The slope is its primitive and vanishes at infinity. -/
theorem refined_variation_integral_eq {a : ℝ} (ha : 3 ≤ a) :
    (∫ t in Set.Ioi a, refinedEulerVariation t) = -refinedEulerSlope a := by
  have ht : Filter.Tendsto refinedEulerSlope Filter.atTop (nhds 0) := by
    have h :=
      refined_slope_times_self_tendsto.mul
        (tendsto_inv_atTop_zero : Filter.Tendsto (fun x : ℝ ↦ x⁻¹) Filter.atTop (nhds 0))
    simp only [zero_mul] at h
    apply h.congr'
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
    rw [mul_comm x (refinedEulerSlope x), mul_assoc, mul_inv_cancel₀ hx.ne', mul_one]
  have h :=
    MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto'
      (fun x hx ↦ refined_slope_derivative (by linarith only [ha, show a ≤ x from hx]))
      (refined_variation_integrable ha) ht
  simpa only [zero_sub] using h

/-- The cutoff-1000 lower bound with the constant-error integral replaced by its boundary slope.
This form leaves only the weight and the square-root and logarithmic variation integrals. -/
theorem quarter_euler_lower_1000_slope (hRH : RiemannHypothesis) :
    (178404 / 100000 : ℝ) * (27 / 25 : ℝ) ^ 5 +
            refinedEulerRealWeight 1000 * (1000 - Chebyshev.psi 1000) +
            refinedEulerSlope 1000 *
              (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum 1000 - 1000) +
            (∫ t in Set.Ioi (1000 : ℝ), refinedEulerRealWeight t) -
          (231 / 5000 : ℝ) * (∫ t in Set.Ioi (1000 : ℝ), Real.sqrt t * refinedEulerVariation t) -
          (1839 / 1000 : ℝ) * (∫ t in Set.Ioi (1000 : ℝ), Real.log t * refinedEulerVariation t) +
        2 * refinedEulerSlope 1000 <
      ∑' n : ℕ, ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n := by
  have h := quarter_euler_centered_lower_1000 hRH
  rw [refined_variation_integral_eq (by norm_num only : (3 : ℝ) ≤ 1000)] at h
  linarith only [h]

/-- The logarithmic variation tail is the weight minus the logarithmic slope at its cutoff.
The primitive tends to zero at infinity, and the integrability is established above. -/
theorem refined_log_variation_integral_eq {a : ℝ} (ha : 3 ≤ a) :
    (∫ t in Set.Ioi a, Real.log t * refinedEulerVariation t) =
      refinedEulerRealWeight a - Real.log a * refinedEulerSlope a := by
  have hlog : Filter.Tendsto (fun x : ℝ ↦ Real.log x / x) Filter.atTop (nhds 0) := by
    simpa only [pow_one] using Analysis.tendsto_log_pow_div_self 1
  have hs :
    Filter.Tendsto (fun x : ℝ ↦ Real.log x * refinedEulerSlope x) Filter.atTop (nhds 0) := by
    have h := refined_slope_times_self_tendsto.mul hlog
    simp only [zero_mul] at h
    apply h.congr'
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
    calc
      (x * refinedEulerSlope x) * (Real.log x / x) = (Real.log x * x / x) * refinedEulerSlope x :=
        by ring
      _ = Real.log x * refinedEulerSlope x := by rw [mul_div_cancel_right₀ _ hx.ne']
  have hw : Filter.Tendsto refinedEulerRealWeight Filter.atTop (nhds 0) := by
    have h :=
      refined_weight_times_self_tendsto.mul
        (tendsto_inv_atTop_zero : Filter.Tendsto (fun x : ℝ ↦ x⁻¹) Filter.atTop (nhds 0))
    simp only [zero_mul] at h
    apply h.congr'
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
    rw [mul_comm x (refinedEulerRealWeight x), mul_assoc, mul_inv_cancel₀ hx.ne', mul_one]
  have ht := hs.sub hw
  simp only [sub_self] at ht
  have hd (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun t : ℝ ↦ Real.log t * refinedEulerSlope t - refinedEulerRealWeight t)
      (Real.log x * refinedEulerVariation x) x := by
    have h :=
      ((Real.hasDerivAt_log hx.ne').mul (refined_slope_derivative hx)).sub
        (refined_weight_derivative hx)
    convert h using 1
    simp only [div_eq_mul_inv]
    ring
  have h :=
    MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto'
      (fun x hx ↦ hd x (by linarith only [ha, show a ≤ x from hx]))
      (refined_log_variation_integrable ha) ht
  linarith only [h]

/-- The cutoff-1000 Euler lower bound with both constant and logarithmic error integrals
replaced by boundary values. Only the weight and square-root variation integrals remain. -/
theorem quarter_euler_lower_1000_boundary (hRH : RiemannHypothesis) :
    (178404 / 100000 : ℝ) * (27 / 25 : ℝ) ^ 5 +
            refinedEulerRealWeight 1000 * (1000 - Chebyshev.psi 1000) +
            refinedEulerSlope 1000 *
              (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum 1000 - 1000) +
            (∫ t in Set.Ioi (1000 : ℝ), refinedEulerRealWeight t) -
          (231 / 5000 : ℝ) * (∫ t in Set.Ioi (1000 : ℝ), Real.sqrt t * refinedEulerVariation t) -
          (1839 / 1000 : ℝ) *
            (refinedEulerRealWeight 1000 - Real.log 1000 * refinedEulerSlope 1000) +
        2 * refinedEulerSlope 1000 <
      ∑' n : ℕ, ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n := by
  have h := quarter_euler_lower_1000_slope hRH
  rw [refined_log_variation_integral_eq (by norm_num only : (3 : ℝ) ≤ 1000)] at h
  exact h

end PseudoPrime.PrimeTestBounds.MillerRabin
