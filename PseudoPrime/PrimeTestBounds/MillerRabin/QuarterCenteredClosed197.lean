/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterEulerTail196
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCenteredFirstEndpoint

/-! Closed-tail residual certificate for radii 196 through 197. -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational logarithm and power checks at the lower radius endpoint. -/
theorem quarter_closed_endpoint_196_checks :
    Analysis.rationalLogIntervalCheck 38416 15 32 0 (105563 / 10000) = true ∧
      AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 38416 0 (111874 / 10000000000) 27
          25 =
        true := by
  decide +kernel

/-- The closed-tail residual satisfies the centered witness inequality on this radius interval. -/
theorem quarter_closed_residual_196_197 {r : ℝ} (hlo : 196 ≤ r) (hhi : r ≤ 197) :
    quarterCenteredClosedResidual r - 57 / 500 - 7 / 250 - (27 / 25 : ℝ) ^ 5 * (33 / 500) ≤
      (27 / 25 : ℝ) ^ 5 * (24439 / 50000 : ℝ) * r - (3 / 4 : ℝ) * r -
        (27 / 25 : ℝ) ^ 5 * (108 / 1000 : ℝ) * Real.sqrt r := by
  have hl := (Analysis.rationalLogIntervalCheck_sound quarter_closed_endpoint_196_checks.1).2
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
        quarter_closed_endpoint_196_checks.2).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl hp
  have hlog : Real.log ((196 : ℝ) ^ 2) ≤ (105563 / 10000 : ℝ) := by
    norm_num only at hl ⊢
    exact hl
  have hpow : ((196 : ℝ) ^ 2) ^ (-(27 / 25 : ℝ)) ≤ (111874 / 10000000000 : ℝ) := by
    norm_num only at hp ⊢
    exact hp
  have hs : (14000 / 1000 : ℝ) ≤ Real.sqrt 196 := Real.le_sqrt_of_sq_le (by norm_num only)
  have ht : Real.sqrt 197 ≤ (14036 / 1000 : ℝ) :=
    Real.sqrt_le_iff.mpr ⟨by norm_num only, by norm_num only⟩
  have h :=
    quarter_centered_gap_first (a := 196) (b := 197) (L := 105563 / 10000) (Q :=
      111874 / 10000000000) (s := 14000 / 1000) (t := 14036 / 1000) (P :=
      (843 / 400 : ℝ) * (27 / 25 : ℝ) ^ 5 - 11533 / 100000 + 7 / 1000 +
        (33 / 2000 : ℝ) * (27 / 25 : ℝ) ^ 5)
      (by norm_num only) hlo hhi hlog hpow (by norm_num only) hs ht
      (by norm_num only [quarterCenteredEndpoint, quarterMomentPolynomial])
  have hc := quarter_euler_tail_196_197 hlo (by linarith only [hhi])
  dsimp only [quarterCenteredClosedResidual, quarterCenteredResidual] at h ⊢
  linarith only [h, hc]

end PseudoPrime.PrimeTestBounds.MillerRabin
