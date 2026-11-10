/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCenteredEndpoint

/-! # Centered scalar gap from radius 164 to 170 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The centered residual is below the scalar margin on `[164,170]`.
Rational logarithm, power and square-root certificates verify the endpoints. -/
theorem quarter_centered_gap_164_170 {r : ℝ} (hlo : 164 ≤ r) (hhi : r ≤ 170) :
    quarterCenteredResidual r - 4 * ((2869 / 1000 : ℝ) - (223 / 125 : ℝ) * (27 / 25 : ℝ) ^ 5) ≤
      (27 / 25 : ℝ) ^ 5 * (24439 / 50000 : ℝ) * r - (3 / 4 : ℝ) * r -
        (27 / 25 : ℝ) ^ 5 * (108 / 1000 : ℝ) * Real.sqrt r := by
  have hl :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 26896 15 32 0 (40799 / 4000) = true from by
          decide +kernel)).2
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
        (show
          AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 26896 0 (1647 / 100000000) 27
              25 =
            true
          from by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl hp
  have hlog : Real.log ((164 : ℝ) ^ 2) ≤ (40799 / 4000 : ℝ) := by
    norm_num only at hl ⊢
    exact hl
  have hpow : ((164 : ℝ) ^ 2) ^ (-(27 / 25 : ℝ)) ≤ (1647 / 100000000 : ℝ) := by
    norm_num only at hp ⊢
    exact hp
  have hs : (6403 / 500 : ℝ) ≤ Real.sqrt 164 := Real.le_sqrt_of_sq_le (by norm_num only)
  have ht : Real.sqrt 170 ≤ (13039 / 1000 : ℝ) :=
    Real.sqrt_le_iff.mpr ⟨by norm_num only, by norm_num only⟩
  apply
    quarter_centered_gap_of_prefix (a := 164) (b := 170) (L := 40799 / 4000) (Q := 1647 / 100000000)
      (s := 6403 / 500) (t := 13039 / 1000) (P := 2869 / 1000) (by norm_num only) hlo hhi hlog hpow
      (by norm_num only) hs ht
  norm_num only [quarterCenteredEndpoint, quarterMomentPolynomial]

end PseudoPrime.PrimeTestBounds.MillerRabin
