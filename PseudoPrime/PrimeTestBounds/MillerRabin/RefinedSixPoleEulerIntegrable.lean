/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleEulerFiniteTail
public import PseudoPrime.LLS.PowerLogTailConvergence

/-! # Integrability of the refined Euler variation tail -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Beyond three, the refined variation density is at most thirteen times
`x^(-109/50)`. Bound the logarithm by five times the fifth root and collect
the nonnegative quadratic terms. This coarse envelope proves convergence;
it is not the numerical tail certificate. -/
theorem refined_variation_coarse {x : ℝ} (hx : 3 ≤ x) :
    refinedEulerVariation x ≤ 13 * x ^ (-(109 / 50 : ℝ)) := by
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
    (4549689 / 1562500 : ℝ) * (Real.log x) ^ 2 + (44793 / 62500 : ℝ) * Real.log x -
        (1041 / 2500 : ℝ) ≤
      104 * x ^ (2 / 5 : ℝ) := by
    rw [← hpow]
    nlinarith only [hl', hsq, hp, hp0, sq_nonneg (x ^ (1 / 5 : ℝ) - 1)]
  have hm := mul_le_mul_of_nonneg_left hpoly (Real.rpow_nonneg hx0.le (-(79 / 50 : ℝ) - 1))
  have hexp : (-(79 / 50 : ℝ) - 1) + 2 / 5 = -(109 / 50 : ℝ) := by norm_num only
  have hm' : x ^ (-(79 / 50 : ℝ) - 1) * (104 * x ^ (2 / 5 : ℝ)) = 104 * x ^ (-(109 / 50 : ℝ)) := by
    rw [show
        x ^ (-(79 / 50 : ℝ) - 1) * (104 * x ^ (2 / 5 : ℝ)) =
          104 * (x ^ (-(79 / 50 : ℝ) - 1) * x ^ (2 / 5 : ℝ))
        by ring,
      ← Real.rpow_add hx0, hexp]
  rw [hm'] at hm
  unfold refinedEulerVariation
  linarith only [hm]

/-- Under RH, the logarithmically weighted Mangoldt sum times the refined
variation density is integrable beyond any cutoff at least three. The
arithmetic sum is bounded by `4t` and the variation by a negative power
with exponent `109/50`; their product has integrable exponent `-59/50`.
This justifies the improper integral in the refined Euler tail. -/
theorem refined_variation_mangoldt_integrable (hRH : RiemannHypothesis) {a : ℝ} (ha : 3 ≤ a) :
    MeasureTheory.IntegrableOn
      (fun t : ℝ ↦
        AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t * refinedEulerVariation t)
      (Set.Ioi a) := by
  have ha0 : 0 < a := by linarith only [ha]
  have hc :
    ContinuousOn
      (fun t : ℝ ↦
        AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t * refinedEulerVariation t)
      (Set.Ioi a) := by
    apply
      ContinuousOn.mul
        (LLS.continuousOn_logWeightedMangoldtSum_Ioi.mono (Set.Ioi_subset_Ioi ha0.le))
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
          52).mono'
      (hc.aestronglyMeasurable measurableSet_Ioi) ?_
  apply MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi
  intro t ht
  have ht3 : (3 : ℝ) ≤ t := ha.trans ht.le
  have ht1 : (1 : ℝ) ≤ t := by linarith only [ht3]
  have ht0 : (0 : ℝ) < t := zero_lt_one.trans_le ht1
  have hS0 := LLS.logWeightedMangoldtSum_nonneg_of_pos ht0
  have hS := LLS.logWeightedMangoldtSum_le_four_mul hRH ht1
  have hV0 := refined_variation_nonneg ht3
  have hV := refined_variation_coarse ht3
  rw [Real.norm_of_nonneg (mul_nonneg hS0 hV0)]
  have hm := mul_le_mul hS hV hV0 (by positivity : 0 ≤ 4 * t)
  have he : (4 * t) * (13 * t ^ (-(109 / 50 : ℝ))) = 52 * t ^ (-(59 / 50 : ℝ)) := by
    rw [show (-(59 / 50 : ℝ)) = -(109 / 50 : ℝ) + 1 by norm_num only, Real.rpow_add_one ht0.ne']
    ring
  exact hm.trans_eq he

end PseudoPrime.PrimeTestBounds.MillerRabin
