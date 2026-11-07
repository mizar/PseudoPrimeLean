/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleEulerIntegral

/-! Explicit square-root variation integral for the refined Euler tail. -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Evaluate the square-root variation integral above any cutoff at least one. -/
theorem refined_sqrt_variation_integral_eq {a : ℝ} (ha : 1 ≤ a) :
    (∫ t in Set.Ioi a, Real.sqrt t * refinedEulerVariation t) =
      a ^ (-(27 / 25 : ℝ)) / 8 *
        ((4549689 / 1562500 : ℝ) *
              ((Real.log a) ^ 2 / (27 / 25 : ℝ) + 2 * Real.log a / (27 / 25 : ℝ) ^ 2 +
                2 / (27 / 25 : ℝ) ^ 3) +
            (44793 / 62500 : ℝ) * (Real.log a / (27 / 25 : ℝ) + 1 / (27 / 25 : ℝ) ^ 2) -
          (1041 / 2500 : ℝ) / (27 / 25 : ℝ)) := by
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  have hr : (0 : ℝ) < 27 / 25 := by norm_num only
  have hp := integrableOn_Ioi_rpow_of_lt (by norm_num only : -(27 / 25 : ℝ) - 1 < -1) ha0
  have h1 := Analysis.log_power_moment_integrable hr ha
  have h2 := Analysis.log_sq_power_integrable hr ha0
  have he :
    (fun t : ℝ ↦
        Real.sqrt t * refinedEulerVariation t) =ᵐ[MeasureTheory.volume.restrict (Set.Ioi a)]
      (fun t : ℝ ↦
        ((4549689 / 1562500 : ℝ) * ((Real.log t) ^ 2 * t ^ (-(27 / 25 : ℝ) - 1)) +
              (44793 / 62500 : ℝ) * (Real.log t * t ^ (-(27 / 25 : ℝ) - 1)) -
            (1041 / 2500 : ℝ) * t ^ (-(27 / 25 : ℝ) - 1)) /
          8) := by
    apply MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi
    intro t ht
    have ht0 := ha0.trans ht
    dsimp only
    unfold refinedEulerVariation
    rw [Real.sqrt_eq_rpow]
    have hx : t ^ (1 / 2 : ℝ) * t ^ (-(79 / 50 : ℝ) - 1) = t ^ (-(27 / 25 : ℝ) - 1) := by
      rw [← Real.rpow_add ht0]
      congr 1
      norm_num only
    rw [show
        t ^ (1 / 2 : ℝ) *
            (t ^ (-(79 / 50 : ℝ) - 1) *
                ((4549689 / 1562500 : ℝ) * (Real.log t) ^ 2 + (44793 / 62500 : ℝ) * Real.log t -
                  (1041 / 2500 : ℝ)) /
              8) =
          (t ^ (1 / 2 : ℝ) * t ^ (-(79 / 50 : ℝ) - 1)) *
              ((4549689 / 1562500 : ℝ) * (Real.log t) ^ 2 + (44793 / 62500 : ℝ) * Real.log t -
                (1041 / 2500 : ℝ)) /
            8
        by ring,
      hx]
    ring
  have hs :
    (∫ t in Set.Ioi a,
        (4549689 / 1562500 : ℝ) * ((Real.log t) ^ 2 * t ^ (-(27 / 25 : ℝ) - 1)) +
            (44793 / 62500 : ℝ) * (Real.log t * t ^ (-(27 / 25 : ℝ) - 1)) -
          (1041 / 2500 : ℝ) * t ^ (-(27 / 25 : ℝ) - 1)) =
      (4549689 / 1562500 : ℝ) * (∫ t in Set.Ioi a, (Real.log t) ^ 2 * t ^ (-(27 / 25 : ℝ) - 1)) +
          (44793 / 62500 : ℝ) * (∫ t in Set.Ioi a, Real.log t * t ^ (-(27 / 25 : ℝ) - 1)) -
        (1041 / 2500 : ℝ) * (∫ t in Set.Ioi a, t ^ (-(27 / 25 : ℝ) - 1)) := by
    have h :=
      MeasureTheory.integral_sub
        ((h2.const_mul (4549689 / 1562500 : ℝ)).add (h1.const_mul (44793 / 62500 : ℝ)))
        (hp.const_mul (1041 / 2500 : ℝ))
    have h' :=
      MeasureTheory.integral_add (h2.const_mul (4549689 / 1562500 : ℝ))
        (h1.const_mul (44793 / 62500 : ℝ))
    simp only [Pi.add_apply, MeasureTheory.integral_const_mul] at h h'
    linarith only [h, h']
  rw [MeasureTheory.integral_congr_ae he, MeasureTheory.integral_div, hs,
    integral_Ioi_rpow_of_lt (by norm_num only : -(27 / 25 : ℝ) - 1 < -1) ha0,
    Analysis.log_power_moment_integral hr ha, Analysis.log_sq_power_integral hr ha0]
  norm_num only
  ring

/-- Under RH, evaluate both improper integrals in the Euler upper bound at 1000. -/
theorem refined_euler_upper_1000_closed (hRH : RiemannHypothesis) :
    (∑' m : ℕ, ArithmeticFunction.vonMangoldt m * refinedSixEulerWeight m) <
      (13107 / 5000 : ℝ) + refinedEulerRealWeight 1000 * (1000 - Chebyshev.psi 1000) +
        refinedEulerSlope 1000 *
          (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum 1000 - 1000) +
        (1000 : ℝ) ^ (-(29 / 50 : ℝ)) / 8 *
          (3 / (29 / 50 : ℝ) +
            (81 / 25 : ℝ) * (Real.log 1000 / (29 / 50 : ℝ) + 1 / (29 / 50 : ℝ) ^ 2) +
            (729 / 625 : ℝ) *
              ((Real.log 1000) ^ 2 / (29 / 50 : ℝ) + 2 * Real.log 1000 / (29 / 50 : ℝ) ^ 2 +
                2 / (29 / 50 : ℝ) ^ 3)) +
        (1 / 20 : ℝ) *
          ((1000 : ℝ) ^ (-(27 / 25 : ℝ)) / 8 *
            ((4549689 / 1562500 : ℝ) *
                  ((Real.log 1000) ^ 2 / (27 / 25 : ℝ) + 2 * Real.log 1000 / (27 / 25 : ℝ) ^ 2 +
                    2 / (27 / 25 : ℝ) ^ 3) +
                (44793 / 62500 : ℝ) * (Real.log 1000 / (27 / 25 : ℝ) + 1 / (27 / 25 : ℝ) ^ 2) -
              (1041 / 2500 : ℝ) / (27 / 25 : ℝ))) := by
  have h := refined_euler_upper_1000_explicit hRH
  rw [refined_sqrt_variation_integral_eq (by norm_num only : (1 : ℝ) ≤ 1000)] at h
  exact h

end PseudoPrime.PrimeTestBounds.MillerRabin
