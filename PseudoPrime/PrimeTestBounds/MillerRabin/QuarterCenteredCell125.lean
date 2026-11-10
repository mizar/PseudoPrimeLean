/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCenteredEndpoint

/-! # Centered scalar gap from radius 125 to 155 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The centered residual is below the scalar margin on `[125,155]`.
Rational logarithm, power and square-root certificates verify the endpoints. -/
theorem quarter_centered_gap_125_155 {r : ℝ} (hlo : 125 ≤ r) (hhi : r ≤ 155) :
    quarterCenteredResidual r - 4 * ((709 / 250 : ℝ) - (223 / 125 : ℝ) * (27 / 25 : ℝ) ^ 5) ≤
      (27 / 25 : ℝ) ^ 5 * (24439 / 50000 : ℝ) * r - (3 / 4 : ℝ) * r -
        (27 / 25 : ℝ) ^ 5 * (108 / 1000 : ℝ) * Real.sqrt r := by
  have hl :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 15625 14 32 0 (30177 / 3125) = true from by
          decide +kernel)).2
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
        (show
          AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 15625 0 (1479 / 50000000) 27
              25 =
            true
          from by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl hp
  have hlog : Real.log ((125 : ℝ) ^ 2) ≤ (30177 / 3125 : ℝ) := by
    norm_num only at hl ⊢
    exact hl
  have hpow : ((125 : ℝ) ^ 2) ^ (-(27 / 25 : ℝ)) ≤ (1479 / 50000000 : ℝ) := by
    norm_num only at hp ⊢
    exact hp
  have hs : (559 / 50 : ℝ) ≤ Real.sqrt 125 := Real.le_sqrt_of_sq_le (by norm_num only)
  have ht : Real.sqrt 155 ≤ (249 / 20 : ℝ) :=
    Real.sqrt_le_iff.mpr ⟨by norm_num only, by norm_num only⟩
  apply
    quarter_centered_gap_of_prefix (a := 125) (b := 155) (L := 30177 / 3125) (Q := 1479 / 50000000)
      (s := 559 / 50) (t := 249 / 20) (P := 709 / 250) (by norm_num only) hlo hhi hlog hpow
      (by norm_num only) hs ht
  norm_num only [quarterCenteredEndpoint, quarterMomentPolynomial]

end PseudoPrime.PrimeTestBounds.MillerRabin
