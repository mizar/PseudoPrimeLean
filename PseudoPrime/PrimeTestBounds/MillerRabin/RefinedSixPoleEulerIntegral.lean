/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.LogPowerMomentIntegral
public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleEulerUpper1000

/-! Explicit integral for the refined Euler weight. -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Evaluate the refined Euler weight integral above a cutoff at least one. -/
theorem refined_weight_integral_eq {a : ℝ} (ha : 1 ≤ a) :
    (∫ t in Set.Ioi a, refinedEulerRealWeight t) =
      a ^ (-(29 / 50 : ℝ)) / 8 *
        (3 / (29 / 50 : ℝ) + (81 / 25 : ℝ) * (Real.log a / (29 / 50 : ℝ) + 1 / (29 / 50 : ℝ) ^ 2) +
          (729 / 625 : ℝ) *
            ((Real.log a) ^ 2 / (29 / 50 : ℝ) + 2 * Real.log a / (29 / 50 : ℝ) ^ 2 +
              2 / (29 / 50 : ℝ) ^ 3)) := by
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  have hr : (0 : ℝ) < 29 / 50 := by norm_num only
  have hp := integrableOn_Ioi_rpow_of_lt (by norm_num only : -(29 / 50 : ℝ) - 1 < -1) ha0
  have h1 := Analysis.log_power_moment_integrable hr ha
  have h2 := Analysis.log_sq_power_integrable hr ha0
  have he :
    refinedEulerRealWeight = fun t : ℝ ↦
      (3 * t ^ (-(29 / 50 : ℝ) - 1) + (81 / 25 : ℝ) * (Real.log t * t ^ (-(29 / 50 : ℝ) - 1)) +
          (729 / 625 : ℝ) * ((Real.log t) ^ 2 * t ^ (-(29 / 50 : ℝ) - 1))) /
        8 := by
    funext t
    unfold refinedEulerRealWeight
    have hx : (-(29 / 50 : ℝ) - 1) = -(79 / 50 : ℝ) := by norm_num only
    rw [hx]
    ring
  have hs :
    (∫ t in Set.Ioi a,
        3 * t ^ (-(29 / 50 : ℝ) - 1) + (81 / 25 : ℝ) * (Real.log t * t ^ (-(29 / 50 : ℝ) - 1)) +
          (729 / 625 : ℝ) * ((Real.log t) ^ 2 * t ^ (-(29 / 50 : ℝ) - 1))) =
      3 * (∫ t in Set.Ioi a, t ^ (-(29 / 50 : ℝ) - 1)) +
        (81 / 25 : ℝ) * (∫ t in Set.Ioi a, Real.log t * t ^ (-(29 / 50 : ℝ) - 1)) +
        (729 / 625 : ℝ) * (∫ t in Set.Ioi a, (Real.log t) ^ 2 * t ^ (-(29 / 50 : ℝ) - 1)) := by
    have h :=
      MeasureTheory.integral_add ((hp.const_mul 3).add (h1.const_mul (81 / 25 : ℝ)))
        (h2.const_mul (729 / 625 : ℝ))
    have h' := MeasureTheory.integral_add (hp.const_mul 3) (h1.const_mul (81 / 25 : ℝ))
    simp only [Pi.add_apply, MeasureTheory.integral_const_mul] at h h'
    linarith only [h, h']
  rw [he, MeasureTheory.integral_div, hs,
    integral_Ioi_rpow_of_lt (by norm_num only : -(29 / 50 : ℝ) - 1 < -1) ha0,
    Analysis.log_power_moment_integral hr ha, Analysis.log_sq_power_integral hr ha0]
  norm_num only
  ring

/-- Under RH, evaluate the weight integral in the Euler upper bound at 1000. -/
theorem refined_euler_upper_1000_explicit (hRH : RiemannHypothesis) :
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
        (1 / 20 : ℝ) * (∫ t in Set.Ioi (1000 : ℝ), Real.sqrt t * refinedEulerVariation t) := by
  have h := refined_euler_upper_1000 hRH
  rw [refined_weight_integral_eq (by norm_num only : (1 : ℝ) ≤ 1000)] at h
  exact h

end PseudoPrime.PrimeTestBounds.MillerRabin
