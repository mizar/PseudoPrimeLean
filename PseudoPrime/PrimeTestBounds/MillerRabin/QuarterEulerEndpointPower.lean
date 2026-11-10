/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleEulerTotal

/-! Tight rational enclosures for the cutoff-1000 powers. -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational interval checks for the three powers at cutoff 1000. These checks support the
sharp Euler lower bound without relying on floating-point evaluations. -/
theorem quarter_euler_power_checks :
    AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 1000 (18197008586 / 1000000000000)
          (18197008587 / 1000000000000) 29 50 =
        true ∧
      AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 1000 (575439937 / 1000000000000)
          (575439938 / 1000000000000) 27 25 =
        true ∧
      AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 1000
          (18197008586 / 1000000000000000) (18197008587 / 1000000000000000) 79 50 =
        true := by
  decide +kernel

/-- The cutoff-1000 powers lie in the checked rational intervals. Soundness of the interval
checks transfers the finite certificates to real inequalities for the Euler lower bound. -/
theorem quarter_euler_power_bounds :
    (18197008586 / 1000000000000 : ℝ) ≤ (1000 : ℝ) ^ (-(29 / 50 : ℝ)) ∧
      (1000 : ℝ) ^ (-(29 / 50 : ℝ)) ≤ 18197008587 / 1000000000000 ∧
      (575439937 / 1000000000000 : ℝ) ≤ (1000 : ℝ) ^ (-(27 / 25 : ℝ)) ∧
      (1000 : ℝ) ^ (-(27 / 25 : ℝ)) ≤ 575439938 / 1000000000000 ∧
      (18197008586 / 1000000000000000 : ℝ) ≤ (1000 : ℝ) ^ (-(79 / 50 : ℝ)) ∧
      (1000 : ℝ) ^ (-(79 / 50 : ℝ)) ≤ 18197008587 / 1000000000000000 := by
  have h1 :=
    AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound quarter_euler_power_checks.1
  have h2 :=
    AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound quarter_euler_power_checks.2.1
  have h3 :=
    AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound quarter_euler_power_checks.2.2
  norm_num only at h1 h2 h3 ⊢
  exact ⟨h1.1, h1.2, h2.1, h2.2, h3.1, h3.2⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
