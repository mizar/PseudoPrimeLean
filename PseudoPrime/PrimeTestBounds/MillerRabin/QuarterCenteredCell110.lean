/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCenteredEndpoint

/-! # Centered scalar gap from radius 110 to 125 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The centered residual is below the scalar margin on `[110,125]`.
Rational logarithm, power and square-root certificates verify the endpoints. -/
theorem quarter_centered_gap_110_125 {r : ℝ} (hlo : 110 ≤ r) (hhi : r ≤ 125) :
    quarterCenteredResidual r ≤
      (27 / 25 : ℝ) ^ 5 * (24439 / 50000 : ℝ) * r - (3 / 4 : ℝ) * r -
        (27 / 25 : ℝ) ^ 5 * (108 / 1000 : ℝ) * Real.sqrt r := by
  have hl :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 12100 14 32 0 (470049 / 50000) = true from by
          decide +kernel)).2
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
        (show
          AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 12100 0 (1949 / 50000000) 27
              25 =
            true
          from by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl hp
  have hlog : Real.log ((110 : ℝ) ^ 2) ≤ (470049 / 50000 : ℝ) := by
    norm_num only at hl ⊢
    exact hl
  have hpow : ((110 : ℝ) ^ 2) ^ (-(27 / 25 : ℝ)) ≤ (1949 / 50000000 : ℝ) := by
    norm_num only at hp ⊢
    exact hp
  have hs : (1311 / 125 : ℝ) ≤ Real.sqrt 110 := Real.le_sqrt_of_sq_le (by norm_num only)
  have ht : Real.sqrt 125 ≤ (11181 / 1000 : ℝ) :=
    Real.sqrt_le_iff.mpr ⟨by norm_num only, by norm_num only⟩
  apply
    quarter_centered_gap_of_endpoint (a := 110) (b := 125) (L := 470049 / 50000) (Q :=
      1949 / 50000000) (s := 1311 / 125) (t := 11181 / 1000) (by norm_num only) hlo hhi hlog hpow
      (by norm_num only) hs ht
  norm_num only [quarterCenteredEndpoint, quarterMomentPolynomial]

end PseudoPrime.PrimeTestBounds.MillerRabin
