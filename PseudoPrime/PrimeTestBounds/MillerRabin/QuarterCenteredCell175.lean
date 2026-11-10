/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCenteredEndpoint

/-! # Centered scalar gap from radius 175 to 178 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The centered residual is below the scalar margin on `[175,178]`.
Rational logarithm, power and square-root certificates verify the endpoints. -/
theorem quarter_centered_gap_175_178 {r : ℝ} (hlo : 175 ≤ r) (hhi : r ≤ 178) :
    quarterCenteredResidual r - 4 * ((1451 / 500 : ℝ) - (223 / 125 : ℝ) * (27 / 25 : ℝ) ^ 5) ≤
      (27 / 25 : ℝ) ^ 5 * (24439 / 50000 : ℝ) * r - (3 / 4 : ℝ) * r -
        (27 / 25 : ℝ) ^ 5 * (108 / 1000 : ℝ) * Real.sqrt r := by
  have hl :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 30625 15 32 0 (1032959 / 100000) = true from by
          decide +kernel)).2
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
        (show
          AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 30625 0 (179 / 12500000) 27
              25 =
            true
          from by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl hp
  have hlog : Real.log ((175 : ℝ) ^ 2) ≤ (1032959 / 100000 : ℝ) := by
    norm_num only at hl ⊢
    exact hl
  have hpow : ((175 : ℝ) ^ 2) ^ (-(27 / 25 : ℝ)) ≤ (179 / 12500000 : ℝ) := by
    norm_num only at hp ⊢
    exact hp
  have hs : (3307 / 250 : ℝ) ≤ Real.sqrt 175 := Real.le_sqrt_of_sq_le (by norm_num only)
  have ht : Real.sqrt 178 ≤ (6671 / 500 : ℝ) :=
    Real.sqrt_le_iff.mpr ⟨by norm_num only, by norm_num only⟩
  apply
    quarter_centered_gap_of_prefix (a := 175) (b := 178) (L := 1032959 / 100000) (Q :=
      179 / 12500000) (s := 3307 / 250) (t := 6671 / 500) (P := 1451 / 500) (by norm_num only) hlo
      hhi hlog hpow (by norm_num only) hs ht
  norm_num only [quarterCenteredEndpoint, quarterMomentPolynomial]

end PseudoPrime.PrimeTestBounds.MillerRabin
