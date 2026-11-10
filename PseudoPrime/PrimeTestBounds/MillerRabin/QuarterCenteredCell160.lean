/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCenteredEndpoint

/-! # Centered scalar gap from radius 160 to 164 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The centered residual is below the scalar margin on `[160,164]`.
Rational logarithm, power and square-root certificates verify the endpoints. -/
theorem quarter_centered_gap_160_164 {r : ℝ} (hlo : 160 ≤ r) (hhi : r ≤ 164) :
    quarterCenteredResidual r - 4 * ((709 / 250 : ℝ) - (223 / 125 : ℝ) * (27 / 25 : ℝ) ^ 5) ≤
      (27 / 25 : ℝ) ^ 5 * (24439 / 50000 : ℝ) * r - (3 / 4 : ℝ) * r -
        (27 / 25 : ℝ) ^ 5 * (108 / 1000 : ℝ) * Real.sqrt r := by
  have hl :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 25600 15 32 0 (253759 / 25000) = true from by
          decide +kernel)).2
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
        (show
          AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 25600 0 (1737 / 100000000) 27
              25 =
            true
          from by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl hp
  have hlog : Real.log ((160 : ℝ) ^ 2) ≤ (253759 / 25000 : ℝ) := by
    norm_num only at hl ⊢
    exact hl
  have hpow : ((160 : ℝ) ^ 2) ^ (-(27 / 25 : ℝ)) ≤ (1737 / 100000000 : ℝ) := by
    norm_num only at hp ⊢
    exact hp
  have hs : (12649 / 1000 : ℝ) ≤ Real.sqrt 160 := Real.le_sqrt_of_sq_le (by norm_num only)
  have ht : Real.sqrt 164 ≤ (12807 / 1000 : ℝ) :=
    Real.sqrt_le_iff.mpr ⟨by norm_num only, by norm_num only⟩
  apply
    quarter_centered_gap_of_prefix (a := 160) (b := 164) (L := 253759 / 25000) (Q :=
      1737 / 100000000) (s := 12649 / 1000) (t := 12807 / 1000) (P := 709 / 250) (by norm_num only)
      hlo hhi hlog hpow (by norm_num only) hs ht
  norm_num only [quarterCenteredEndpoint, quarterMomentPolynomial]

end PseudoPrime.PrimeTestBounds.MillerRabin
