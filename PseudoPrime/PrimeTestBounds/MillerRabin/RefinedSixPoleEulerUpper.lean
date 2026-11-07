/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleEulerCentered
public import PseudoPrime.LLS.RiemannWeightedUpperBounds

/-! One-sided RH bound for the refined Euler tail. -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The square-root weighted variation is integrable above any cutoff at least three. -/
theorem refined_sqrt_variation_integrable {a : ℝ} (ha : 3 ≤ a) :
    MeasureTheory.IntegrableOn (fun t : ℝ ↦ Real.sqrt t * refinedEulerVariation t) (Set.Ioi a) := by
  have ha0 : 0 < a := by linarith only [ha]
  have hc : ContinuousOn (fun t : ℝ ↦ Real.sqrt t * refinedEulerVariation t) (Set.Ioi a) := by
    apply ContinuousOn.mul Real.continuous_sqrt.continuousOn
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
  have ht1 : (1 : ℝ) ≤ t := by linarith only [ht3]
  have hv := refined_variation_nonneg ht3
  rw [Real.norm_of_nonneg (mul_nonneg (Real.sqrt_nonneg t) hv)]
  have hs : Real.sqrt t ≤ t := by
    nlinarith only [Real.sqrt_nonneg t, Real.sq_sqrt (zero_le_one.trans ht1), ht1,
      sq_nonneg (t - 1)]
  exact mul_le_mul_of_nonneg_right hs hv

/-- Under RH, bound the centered Euler error by a square-root variation integral. -/
theorem refined_euler_centered_upper (hRH : RiemannHypothesis) {a : ℝ} (ha : 3 ≤ a) :
    (∑' m : ℕ, ArithmeticFunction.vonMangoldt m * refinedSixEulerWeight m) ≤
      (∑ m ∈ Finset.Ioc 0 ⌊a⌋₊, ArithmeticFunction.vonMangoldt m * refinedSixEulerWeight m) +
        refinedEulerRealWeight a * (a - Chebyshev.psi a) +
        refinedEulerSlope a * (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum a - a) +
        (∫ t in Set.Ioi a, refinedEulerRealWeight t) +
        (1 / 20 : ℝ) * (∫ t in Set.Ioi a, Real.sqrt t * refinedEulerVariation t) := by
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
    rw [he]; exact hi
  have hu := (refined_sqrt_variation_integrable ha).const_mul (1 / 20 : ℝ)
  have hb :
    (∫ t in Set.Ioi a,
        (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t - t) * refinedEulerVariation t) ≤
      ∫ t in Set.Ioi a, (1 / 20 : ℝ) * (Real.sqrt t * refinedEulerVariation t) := by
    apply MeasureTheory.integral_mono_ae hi' hu
    apply MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi
    intro t ht
    have ht3 : (3 : ℝ) ≤ t := ha.trans ht.le
    have ht1 : (1 : ℝ) < t := by linarith only [ht3]
    have hs := LLS.logWeightedMangoldtSum_le_add_sqrt_twentieth hRH ht1
    have hv := refined_variation_nonneg ht3
    nlinarith only [mul_le_mul_of_nonneg_right
        (show AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t - t ≤ Real.sqrt t / 20 by
          linarith only [hs])
        hv]
  rw [MeasureTheory.integral_const_mul] at hb
  rw [refined_euler_centered_tail hRH ha]
  linarith only [hb]

end PseudoPrime.PrimeTestBounds.MillerRabin
