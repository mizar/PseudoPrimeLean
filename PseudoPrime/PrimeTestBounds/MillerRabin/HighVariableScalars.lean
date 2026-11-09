/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-! # Scalar coefficient and logarithmic estimates -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The variable radius coefficient at logarithmic scale `U`. It solves the paired-count gap
equation with a margin of `1 / 100`; the intended input is `2 * log L` for the high range. -/
noncomputable def pairedAlpha (U : ℝ) : ℝ :=
  (U + 1 / 100) / ((3 / 2) * U + 339 / 500)

/-- For `U ≥ 22`, the variable coefficient lies between `647 / 1000` and `2 / 3`. Positivity of
the denominator reduces both comparisons to linear inequalities; the bounds make it admissible
for the large-cofactor counting estimates. -/
theorem pairedAlpha_bounds {U : ℝ} (hU : 22 ≤ U) :
    (647 / 1000 : ℝ) ≤ pairedAlpha U ∧ pairedAlpha U ≤ 2 / 3 := by
  have hd : 0 < (3 / 2 : ℝ) * U + 339 / 500 := by linarith only [hU]
  dsimp only [pairedAlpha]
  constructor
  · apply (le_div_iff₀ hd).mpr
    linarith only [hU]
  · apply (div_le_iff₀ hd).mpr
    linarith only [hU]

/-- At `U ≥ 22`, the variable coefficient attains the exact `1 / 100` paired-count gap. Clearing
the positive denominator proves the identity and supplies the scalar hypothesis of the
large-cofactor witness theorem. -/
theorem pairedAlpha_gap {U : ℝ} (hU : 22 ≤ U) :
    (3 / 2 * pairedAlpha U - 1) * U + (339 / 500) * pairedAlpha U = 1 / 100 := by
  have hd : (3 / 2 : ℝ) * U + 339 / 500 ≠ 0 := by
    have hp : 0 < (3 / 2 : ℝ) * U + 339 / 500 := by linarith only [hU]
    exact hp.ne'
  have he : pairedAlpha U * ((3 / 2 : ℝ) * U + 339 / 500) = U + 1 / 100 := by
    dsimp only [pairedAlpha]
    exact div_mul_cancel₀ _ hd
  nlinarith only [he]

/-- The variable coefficient is at least `653 / 1000` for `U ≥ 22`. This sharper endpoint
bound supplies the lower scale required by the Gaussian three-factor comparison. -/
theorem pairedAlpha_ge_653 {U : ℝ} (hU : 22 ≤ U) : (653 / 1000 : ℝ) ≤ pairedAlpha U := by
  have hd : 0 < (3 / 2 : ℝ) * U + 339 / 500 := by linarith only [hU]
  dsimp only [pairedAlpha]
  apply (le_div_iff₀ hd).mpr
  linarith only [hU]

/-- For `L ≥ 70000`, twice its logarithm is at least 22. Compare with `2 ^ 16` and use the
certified lower bound for `log 2`; this verifies the domain of `pairedAlpha`. -/
theorem high_log_twice_ge_22 {L : ℝ} (hL : 70000 ≤ L) : 22 ≤ 2 * Real.log L := by
  have hl :=
    Real.log_le_log (by norm_num only : (0 : ℝ) < 2 ^ 16)
      (show (2 : ℝ) ^ 16 ≤ L by nlinarith only [hL])
  rw [Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  linarith only [hl, Real.log_two_gt_d9]

/-- For `22 ≤ U ≤ 24`, the paired radius coefficient is at most `33 / 50`. Clearing the positive
denominator gives a rational upper bound sufficient for a strict comparison with `7 / 16`. -/
theorem pairedAlpha_le_33_50 {U : ℝ} (hL : 22 ≤ U) (hU : U ≤ 24) : pairedAlpha U ≤ 33 / 50 := by
  have hd : 0 < (3 / 2 : ℝ) * U + 339 / 500 := by linarith only [hL]
  dsimp only [pairedAlpha]
  apply (div_le_iff₀ hd).mpr
  linarith only [hU]

end PseudoPrime.PrimeTestBounds.MillerRabin
