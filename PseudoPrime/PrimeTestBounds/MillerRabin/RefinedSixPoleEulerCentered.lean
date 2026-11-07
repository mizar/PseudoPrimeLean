/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleEulerInfiniteTail

/-! Centered double-Abel identity for the refined Euler sum. -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The variation density times the identity is integrable beyond a cutoff of at least three. -/
theorem refined_linear_variation_integrable {a : ℝ} (ha : 3 ≤ a) :
    MeasureTheory.IntegrableOn (fun t : ℝ ↦ t * refinedEulerVariation t) (Set.Ioi a) := by
  have ha0 : 0 < a := by linarith only [ha]
  have hc : ContinuousOn (fun t : ℝ ↦ t * refinedEulerVariation t) (Set.Ioi a) := by
    apply ContinuousOn.mul continuousOn_id
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
    ((integrableOn_Ioi_rpow_of_lt (by norm_num only : (-(59 / 50 : ℝ)) < -1) ha0).const_mul
          13).mono'
      (hc.aestronglyMeasurable measurableSet_Ioi) ?_
  apply MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi
  intro t ht
  have ht3 : (3 : ℝ) ≤ t := ha.trans ht.le
  have ht0 : 0 ≤ t := by linarith only [ht3]
  rw [Real.norm_of_nonneg (mul_nonneg ht0 (refined_variation_nonneg ht3))]
  have hm := mul_le_mul_of_nonneg_left (refined_variation_coarse ht3) ht0
  have he : t * (13 * t ^ (-(109 / 50 : ℝ))) = 13 * t ^ (-(59 / 50 : ℝ)) := by
    rw [show (-(59 / 50 : ℝ)) = -(109 / 50 : ℝ) + 1 by norm_num only,
      Real.rpow_add_one (by linarith only [ht3] : t ≠ 0)]
    ring
  exact hm.trans_eq he

/-- Beyond three, a negative power bounds the refined Euler weight. -/
theorem refined_weight_coarse {x : ℝ} (hx : 3 ≤ x) :
    refinedEulerRealWeight x ≤ 7 * x ^ (-(59 / 50 : ℝ)) := by
  have hx1 : (1 : ℝ) ≤ x := by linarith only [hx]
  have hx0 : 0 < x := zero_lt_one.trans_le hx1
  have hl0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hl := Real.log_le_rpow_div hx0.le (by norm_num only : (0 : ℝ) < 1 / 5)
  have hp : 1 ≤ x ^ (1 / 5 : ℝ) := Real.one_le_rpow hx1 (by norm_num only)
  have hp0 : 0 ≤ x ^ (1 / 5 : ℝ) := Real.rpow_nonneg hx0.le _
  have hl' : Real.log x ≤ 5 * x ^ (1 / 5 : ℝ) := by linarith only [hl]
  have hsq := pow_le_pow_left₀ hl0 hl' 2
  have hpow : (x ^ (1 / 5 : ℝ)) ^ (2 : ℕ) = x ^ (2 / 5 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    norm_num only
  have hpoly :
    3 + (81 / 25 : ℝ) * Real.log x + (729 / 625 : ℝ) * (Real.log x) ^ 2 ≤ 56 * x ^ (2 / 5 : ℝ) := by
    rw [← hpow]
    nlinarith only [hl', hsq, hp, hp0, sq_nonneg (x ^ (1 / 5 : ℝ) - 1)]
  have hm := mul_le_mul_of_nonneg_left hpoly (Real.rpow_nonneg hx0.le (-(79 / 50 : ℝ)))
  have hm' : x ^ (-(79 / 50 : ℝ)) * (56 * x ^ (2 / 5 : ℝ)) = 56 * x ^ (-(59 / 50 : ℝ)) := by
    rw [show
        x ^ (-(79 / 50 : ℝ)) * (56 * x ^ (2 / 5 : ℝ)) =
          56 * (x ^ (-(79 / 50 : ℝ)) * x ^ (2 / 5 : ℝ))
        by ring,
      ← Real.rpow_add hx0]
    norm_num only
  rw [hm'] at hm
  unfold refinedEulerRealWeight
  linarith only [hm]

/-- The refined Euler weight is integrable beyond any cutoff at least three. -/
theorem refined_weight_integrable {a : ℝ} (ha : 3 ≤ a) :
    MeasureTheory.IntegrableOn refinedEulerRealWeight (Set.Ioi a) := by
  have ha0 : 0 < a := by linarith only [ha]
  have hc : ContinuousOn refinedEulerRealWeight (Set.Ioi a) := by
    intro t ht
    exact (refined_weight_derivative (ha0.trans ht)).continuousAt.continuousWithinAt
  refine
    ((integrableOn_Ioi_rpow_of_lt (by norm_num only : (-(59 / 50 : ℝ)) < -1) ha0).const_mul 7).mono'
      (hc.aestronglyMeasurable measurableSet_Ioi) ?_
  apply MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi
  intro t ht
  have ht3 : (3 : ℝ) ≤ t := ha.trans ht.le
  have ht1 : (1 : ℝ) ≤ t := by linarith only [ht3]
  have hl := Real.log_nonneg ht1
  have hw : 0 ≤ refinedEulerRealWeight t := by
    unfold refinedEulerRealWeight
    apply div_nonneg
    · apply mul_nonneg (Real.rpow_nonneg (zero_le_one.trans ht1) _)
      nlinarith only [hl, sq_nonneg (Real.log t)]
    · norm_num only
  rw [Real.norm_of_nonneg hw]
  exact refined_weight_coarse ht3

/-- On a positive finite interval, integrate the linear variation using the weight derivative. -/
theorem refined_linear_variation_finite {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, t * refinedEulerVariation t) =
      b * refinedEulerSlope b - b * refinedEulerRealWeight b -
          (a * refinedEulerSlope a - a * refinedEulerRealWeight a) +
        ∫ t in a..b, refinedEulerRealWeight t := by
  have hv :
    ∀ t ∈ Set.uIcc a b, HasDerivAt refinedEulerRealWeight (deriv refinedEulerRealWeight t) t := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    exact
      (refined_weight_derivative (ha.trans_le ht.1)).deriv ▸
        refined_weight_derivative (ha.trans_le ht.1)
  have hp :
    ∀ t ∈ Set.uIcc a b,
      HasDerivAt (fun u : ℝ ↦ u * deriv refinedEulerRealWeight u) (refinedEulerVariation t) t := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    exact refined_weight_log_variation (ha.trans_le ht.1)
  have hiQ :
    IntervalIntegrable (fun t : ℝ ↦ t * refinedEulerVariation t) MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    apply ContinuousOn.mul continuousOn_id
    intro t ht
    have ht0 := ha.trans_le ht.1
    unfold refinedEulerVariation
    exact
      (((Real.continuousAt_rpow_const t (-(79 / 50 : ℝ) - 1) (Or.inl ht0.ne')).mul
              (((continuousAt_const.mul ((Real.continuousAt_log ht0.ne').pow 2)).add
                    (continuousAt_const.mul (Real.continuousAt_log ht0.ne'))).sub
                continuousAt_const)).div_const
          8).continuousWithinAt
  have hiV : IntervalIntegrable refinedEulerRealWeight MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    intro t ht
    exact (refined_weight_derivative (ha.trans_le ht.1)).continuousAt.continuousWithinAt
  have h := Analysis.linear_variation_integral hv hp hiQ hiV
  rw [(refined_weight_derivative ha).deriv,
    (refined_weight_derivative (ha.trans_le hab)).deriv] at h
  rw [mul_div_cancel₀ _ ha.ne', mul_div_cancel₀ _ (ha.trans_le hab).ne'] at h
  exact h

/-- At a cutoff at least three, the linear variation integral equals the weight integral
and boundary term. -/
theorem refined_linear_variation_infinite {a : ℝ} (ha : 3 ≤ a) :
    (∫ t in Set.Ioi a, t * refinedEulerVariation t) =
      -(a * refinedEulerSlope a - a * refinedEulerRealWeight a) +
        ∫ t in Set.Ioi a, refinedEulerRealWeight t := by
  have ha0 : 0 < a := by linarith only [ha]
  have hi :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi a (refined_linear_variation_integrable ha)
      Filter.tendsto_id
  have hw :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi a (refined_weight_integrable ha)
      Filter.tendsto_id
  have hb :=
    (refined_slope_times_self_tendsto.sub refined_weight_times_self_tendsto) |>.sub_const
      (a * refinedEulerSlope a - a * refinedEulerRealWeight a)
  have hr := hb.add hw
  simp only [sub_zero, zero_sub] at hr
  have he :
    (fun b : ℝ ↦ ∫ t in a..b, t * refinedEulerVariation t) =ᶠ[Filter.atTop]
      (fun b : ℝ ↦
        b * refinedEulerSlope b - b * refinedEulerRealWeight b -
            (a * refinedEulerSlope a - a * refinedEulerRealWeight a) +
          ∫ t in a..b, refinedEulerRealWeight t) := by
    filter_upwards [Filter.eventually_ge_atTop a] with b hb
    exact refined_linear_variation_finite ha0 hb
  exact tendsto_nhds_unique (hi.congr' he) hr

/-- Under RH, express the Euler sum using the finite prefix, boundary corrections,
and centered error integral. -/
theorem refined_euler_centered_tail (hRH : RiemannHypothesis) {a : ℝ} (ha : 3 ≤ a) :
    (∑' m : ℕ, ArithmeticFunction.vonMangoldt m * refinedSixEulerWeight m) =
      (∑ m ∈ Finset.Ioc 0 ⌊a⌋₊, ArithmeticFunction.vonMangoldt m * refinedSixEulerWeight m) +
        refinedEulerRealWeight a * (a - Chebyshev.psi a) +
        refinedEulerSlope a * (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum a - a) +
        (∫ t in Set.Ioi a, refinedEulerRealWeight t) +
        (∫ t in Set.Ioi a,
          (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t - t) *
            refinedEulerVariation t) := by
  have hi := refined_variation_mangoldt_integrable hRH ha
  have hl := refined_linear_variation_integrable ha
  have he :
    (fun t : ℝ ↦
        (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t - t) * refinedEulerVariation t) =
      (fun t : ℝ ↦
        AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t * refinedEulerVariation t -
          t * refinedEulerVariation t) := by
    funext t
    ring
  rw [he, MeasureTheory.integral_sub hi hl]
  have ht := refined_euler_infinite_tail hRH ha
  have hv := refined_linear_variation_infinite ha
  linarith only [ht, hv]

end PseudoPrime.PrimeTestBounds.MillerRabin
