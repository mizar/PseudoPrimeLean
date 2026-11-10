/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCenteredEndpoint

/-! # Centered scalar gap from radius 70 to 110 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The centered residual is below the scalar margin on `[70,110]`.
Rational logarithm, power and square-root certificates verify the endpoints. -/
theorem quarter_centered_gap_70_110 {r : ℝ} (hlo : 70 ≤ r) (hhi : r ≤ 110) :
    quarterCenteredResidual r ≤
      (27 / 25 : ℝ) ^ 5 * (24439 / 50000 : ℝ) * r - (3 / 4 : ℝ) * r -
        (27 / 25 : ℝ) ^ 5 * (108 / 1000 : ℝ) * Real.sqrt r := by
  have hl :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 4900 12 32 0 (849701 / 100000) = true from by
          decide +kernel)).2
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
        (show
          AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 4900 0 (1293 / 12500000) 27
              25 =
            true
          from by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl hp
  have hlog : Real.log ((70 : ℝ) ^ 2) ≤ (849701 / 100000 : ℝ) := by
    norm_num only at hl ⊢
    exact hl
  have hpow : ((70 : ℝ) ^ 2) ^ (-(27 / 25 : ℝ)) ≤ (1293 / 12500000 : ℝ) := by
    norm_num only at hp ⊢
    exact hp
  have hs : (4183 / 500 : ℝ) ≤ Real.sqrt 70 := Real.le_sqrt_of_sq_le (by norm_num only)
  have ht : Real.sqrt 110 ≤ (10489 / 1000 : ℝ) :=
    Real.sqrt_le_iff.mpr ⟨by norm_num only, by norm_num only⟩
  apply
    quarter_centered_gap_of_endpoint (a := 70) (b := 110) (L := 849701 / 100000) (Q :=
      1293 / 12500000) (s := 4183 / 500) (t := 10489 / 1000) (by norm_num only) hlo hhi hlog hpow
      (by norm_num only) hs ht
  norm_num only [quarterCenteredEndpoint, quarterMomentPolynomial]

end PseudoPrime.PrimeTestBounds.MillerRabin
