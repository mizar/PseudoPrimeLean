/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterEulerMomentLower
public import PseudoPrime.Analysis.LogPowerIntervalIntegral

/-! # Explicit finite Euler moment integrals -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The explicit power-logarithm integral on `[1000,b]` used in the Euler
moment lower bounds. It is a difference of four endpoint polynomials. -/
noncomputable def quarterEulerMomentIntegral (k : ℕ) (b : ℝ) : ℝ :=
  ((1000 : ℝ) ^ (-(29 / 50 : ℝ)) * Analysis.logPowerTailPoly (29 / 50) k (Real.log 1000) -
      b ^ (-(29 / 50 : ℝ)) * Analysis.logPowerTailPoly (29 / 50) k (Real.log b)) -
    (3 / 4 : ℝ) *
      ((1000 : ℝ) ^ (-(83 / 100 : ℝ)) * Analysis.logPowerTailPoly (83 / 100) k (Real.log 1000) -
        b ^ (-(83 / 100 : ℝ)) * Analysis.logPowerTailPoly (83 / 100) k (Real.log b))

/-- Evaluate the Chebyshev lower-envelope integral by the general finite
power-logarithm primitive. Both exponents are positive at the lower cutoff. -/
theorem quarter_euler_moment_integral_eq (k : ℕ) {b : ℝ} (hb : (1000 : ℝ) ≤ b) :
    (∫ t in Set.Ioc (1000 : ℝ) b,
        (1 - (3 / 4 : ℝ) * t ^ (-(1 / 4 : ℝ))) *
          AnalyticNumberTheory.Arithmetic.mangoldtMomentWeight (79 / 50) k t) =
      quarterEulerMomentIntegral k b := by
  have hi1 :
    MeasureTheory.IntegrableOn (fun t : ℝ ↦ Real.log t ^ k * t ^ (-(29 / 50 : ℝ) - 1))
      (Set.Ioc 1000 b) :=
    (Analysis.log_power_tail_integrable (by norm_num only : (0 : ℝ) < 29 / 50)
          (by norm_num only : (1 : ℝ) ≤ 1000) k).mono_set
      Set.Ioc_subset_Ioi_self
  have hi2 :
    MeasureTheory.IntegrableOn (fun t : ℝ ↦ Real.log t ^ k * t ^ (-(83 / 100 : ℝ) - 1))
      (Set.Ioc 1000 b) :=
    (Analysis.log_power_tail_integrable (by norm_num only : (0 : ℝ) < 83 / 100)
          (by norm_num only : (1 : ℝ) ≤ 1000) k).mono_set
      Set.Ioc_subset_Ioi_self
  have he :
    (∫ t in Set.Ioc (1000 : ℝ) b,
        (1 - (3 / 4 : ℝ) * t ^ (-(1 / 4 : ℝ))) *
          AnalyticNumberTheory.Arithmetic.mangoldtMomentWeight (79 / 50) k t) =
      ∫ t in Set.Ioc (1000 : ℝ) b,
        (Real.log t ^ k * t ^ (-(29 / 50 : ℝ) - 1) -
          (3 / 4 : ℝ) * (Real.log t ^ k * t ^ (-(83 / 100 : ℝ) - 1))) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    have ht0 : 0 < t := by linarith only [ht.1]
    have hp : t ^ (-(1 / 4 : ℝ)) * t ^ (-(79 / 50 : ℝ)) = t ^ (-(83 / 100 : ℝ) - 1) := by
      rw [← Real.rpow_add ht0]
      norm_num only
    dsimp only [AnalyticNumberTheory.Arithmetic.mangoldtMomentWeight]
    norm_num only at ⊢
    have hp' := congrArg (fun z : ℝ ↦ Real.log t ^ k * z) hp
    norm_num only at hp'
    ring_nf at hp' ⊢
    linarith only [hp']
  rw [he, MeasureTheory.integral_sub hi1 (hi2.const_mul (3 / 4 : ℝ)),
    MeasureTheory.integral_const_mul,
    Analysis.log_power_interval_integral (by norm_num only : (0 : ℝ) < 29 / 50)
      (by norm_num only : (1 : ℝ) ≤ 1000) hb,
    Analysis.log_power_interval_integral (by norm_num only : (0 : ℝ) < 83 / 100)
      (by norm_num only : (1 : ℝ) ≤ 1000) hb]
  rfl

end PseudoPrime.PrimeTestBounds.MillerRabin
