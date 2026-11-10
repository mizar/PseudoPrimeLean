/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentFromIntegrals
public import PseudoPrime.Analysis.LogPowerTailIntegral
public import PseudoPrime.Analysis.PreciseLogTaylorBounds

/-! # Explicit reflected moment tail integrals -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The reflected tail integral is the sum of two logarithmic-power tail
polynomials, with decay rates `29/50` and `83/100`. -/
theorem quarter_moment_integral_eq (k : ℕ) :
    (∫ t in Set.Ioi (2701 : ℝ), quarterMomentTailIntegrand k t) =
      (2701 : ℝ) ^ (-(29 / 50 : ℝ)) * Analysis.logPowerTailPoly (29 / 50) k (Real.log 2701) +
        (3 / 4 : ℝ) *
          ((2701 : ℝ) ^ (-(83 / 100 : ℝ)) *
            Analysis.logPowerTailPoly (83 / 100) k (Real.log 2701)) := by
  have hi1 :=
    Analysis.log_power_tail_integrable (r := 29 / 50) (a := 2701) (by norm_num only)
      (by norm_num only) k
  have hi2 :=
    Analysis.log_power_tail_integrable (r := 83 / 100) (a := 2701) (by norm_num only)
      (by norm_num only) k
  have he :
    ∀ t ∈ Set.Ioi (2701 : ℝ),
      quarterMomentTailIntegrand k t =
        Real.log t ^ k * t ^ (-(29 / 50 : ℝ) - 1) +
          (3 / 4 : ℝ) * (Real.log t ^ k * t ^ (-(83 / 100 : ℝ) - 1)) := by
    intro t ht
    change (2701 : ℝ) < t at ht
    have ht0 : 0 < t := by linarith only [ht]
    have hp : t ^ (-(1 / 4 : ℝ)) * t ^ (-(79 / 50 : ℝ)) = t ^ (-(83 / 100 : ℝ) - 1) := by
      rw [← Real.rpow_add ht0]
      norm_num only
    have hp1 : (-(29 / 50 : ℝ) - 1) = -(79 / 50 : ℝ) := by norm_num only
    dsimp only [quarterMomentTailIntegrand, AnalyticNumberTheory.Arithmetic.mangoldtMomentWeight]
    rw [hp1]
    calc
      _ =
          Real.log t ^ k * t ^ (-(79 / 50 : ℝ)) +
            (3 / 4 : ℝ) * (Real.log t ^ k * (t ^ (-(1 / 4 : ℝ)) * t ^ (-(79 / 50 : ℝ)))) :=
        by ring
      _ = _ := by rw [hp]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi he,
    MeasureTheory.integral_add hi1 (hi2.const_mul (3 / 4 : ℝ)), MeasureTheory.integral_const_mul,
    Analysis.log_power_tail_integral (r := 29 / 50) (a := 2701) (by norm_num only)
      (by norm_num only),
    Analysis.log_power_tail_integral (r := 83 / 100) (a := 2701) (by norm_num only)
      (by norm_num only)]

/-- Six explicit tail-integral caps follow from the general integral formula
and kernel-checked rational logarithm and real-power endpoints. -/
theorem quarter_moment_integral_bounds : QuarterMomentIntegralBounds := by
  intro k hk
  have hlog :=
    (Analysis.preciseLogCheck_sound
        (show Analysis.preciseLogCheck 2701 12 64 0 (7901377353793 / 1000000000000) = true from by
          decide +kernel)).2
  have hp1 :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
        (show
          AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 2701 0
              (10226234353202 / 1000000000000000) 29 50 =
            true
          from by decide +kernel)).2
  have hp2 :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
        (show
          AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 2701 0
              (1418517164050 / 1000000000000000) 83 100 =
            true
          from by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlog hp1 hp2
  have hl : Real.log 2701 ≤ (7901377353793 / 1000000000000 : ℝ) := by
    norm_num only at hlog ⊢
    exact hlog
  have h1 : (2701 : ℝ) ^ (-(29 / 50 : ℝ)) ≤ (10226234353202 / 1000000000000000 : ℝ) := by
    norm_num only at hp1 ⊢
    exact hp1
  have h2 : (2701 : ℝ) ^ (-(83 / 100 : ℝ)) ≤ (1418517164050 / 1000000000000000 : ℝ) := by
    norm_num only at hp2 ⊢
    exact hp2
  have hz : 0 ≤ Real.log 2701 := Real.log_nonneg (by norm_num only)
  have hpoly1 := Analysis.log_power_tail_poly_mono (r := (29 / 50 : ℝ)) (by norm_num only) hz hl k
  have hpoly2 := Analysis.log_power_tail_poly_mono (r := (83 / 100 : ℝ)) (by norm_num only) hz hl k
  have hpoly10 := Analysis.log_power_tail_poly_nonneg (r := (29 / 50 : ℝ)) (by norm_num only) hz k
  have hpoly20 := Analysis.log_power_tail_poly_nonneg (r := (83 / 100 : ℝ)) (by norm_num only) hz k
  have hb1 :=
    mul_le_mul h1 hpoly1 hpoly10 (by norm_num only : (0 : ℝ) ≤ 10226234353202 / 1000000000000000)
  have hb2 :=
    mul_le_mul h2 hpoly2 hpoly20 (by norm_num only : (0 : ℝ) ≤ 1418517164050 / 1000000000000000)
  have hnum :
    (10226234353202 / 1000000000000000 : ℝ) *
          Analysis.logPowerTailPoly (29 / 50) k (7901377353793 / 1000000000000) +
        (3 / 4 : ℝ) *
          ((1418517164050 / 1000000000000000 : ℝ) *
            Analysis.logPowerTailPoly (83 / 100) k (7901377353793 / 1000000000000)) ≤
      quarterMomentIntegralCap k := by
    interval_cases k <;> norm_num only [Analysis.logPowerTailPoly, quarterMomentIntegralCap]
  rw [quarter_moment_integral_eq]
  linarith only [hb1, hb2, hnum]

end PseudoPrime.PrimeTestBounds.MillerRabin
