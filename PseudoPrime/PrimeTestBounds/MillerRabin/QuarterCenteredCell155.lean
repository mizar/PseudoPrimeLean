/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCenteredEndpoint

/-! # Centered scalar gap from radius 155 to 160 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The centered residual is below the scalar margin on `[155,160]`.
Rational logarithm, power and square-root certificates verify the endpoints. -/
theorem quarter_centered_gap_155_160 {r : ℝ} (hlo : 155 ≤ r) (hhi : r ≤ 160) :
    quarterCenteredResidual r - 4 * ((709 / 250 : ℝ) - (223 / 125 : ℝ) * (27 / 25 : ℝ) ^ 5) ≤
      (27 / 25 : ℝ) ^ 5 * (24439 / 50000 : ℝ) * r - (3 / 4 : ℝ) * r -
        (27 / 25 : ℝ) ^ 5 * (108 / 1000 : ℝ) * Real.sqrt r := by
  have hl :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 24025 15 32 0 (1008687 / 100000) = true from by
          decide +kernel)).2
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
        (show
          AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 24025 0 (93 / 5000000) 27 25 =
            true
          from by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl hp
  have hlog : Real.log ((155 : ℝ) ^ 2) ≤ (1008687 / 100000 : ℝ) := by
    norm_num only at hl ⊢
    exact hl
  have hpow : ((155 : ℝ) ^ 2) ^ (-(27 / 25 : ℝ)) ≤ (93 / 5000000 : ℝ) := by
    norm_num only at hp ⊢
    exact hp
  have hs : (12449 / 1000 : ℝ) ≤ Real.sqrt 155 := Real.le_sqrt_of_sq_le (by norm_num only)
  have ht : Real.sqrt 160 ≤ (253 / 20 : ℝ) :=
    Real.sqrt_le_iff.mpr ⟨by norm_num only, by norm_num only⟩
  apply
    quarter_centered_gap_of_prefix (a := 155) (b := 160) (L := 1008687 / 100000) (Q := 93 / 5000000)
      (s := 12449 / 1000) (t := 253 / 20) (P := 709 / 250) (by norm_num only) hlo hhi hlog hpow
      (by norm_num only) hs ht
  norm_num only [quarterCenteredEndpoint, quarterMomentPolynomial]

end PseudoPrime.PrimeTestBounds.MillerRabin
