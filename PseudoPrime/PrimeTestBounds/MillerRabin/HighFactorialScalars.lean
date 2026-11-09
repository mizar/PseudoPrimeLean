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
public import PseudoPrime.PrimeTestBounds.MillerRabin.HighVariableScalars

/-! # Scalar coefficient and logarithmic estimates -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The factorial-based radius coefficient at logarithmic scale `U`. It solves the strengthened
cofactor counting gap with margin `3 / 200`; its intended input is `2 * log L`. -/
noncomputable def factorialAlpha (U : ℝ) : ℝ :=
  (U + 3 / 200) / ((3 / 2) * U + 49 / 50)

/-- For `U ≥ 22`, the factorial coefficient lies between `647 / 1000` and `2 / 3`. Clearing the
positive denominator reduces both estimates to rational linear inequalities. -/
theorem factorialAlpha_bounds {U : ℝ} (hU : 22 ≤ U) :
    (647 / 1000 : ℝ) ≤ factorialAlpha U ∧ factorialAlpha U ≤ 2 / 3 := by
  have hd : 0 < (3 / 2 : ℝ) * U + 49 / 50 := by linarith only [hU]
  dsimp only [factorialAlpha]
  constructor
  · apply (le_div_iff₀ hd).mpr
    linarith only [hU]
  · apply (div_le_iff₀ hd).mpr
    linarith only [hU]

/-- For `U ≥ 22`, the factorial coefficient attains the exact `3 / 200` counting gap. This
identity is the scalar input for the factorial cofactor budget. -/
theorem factorialAlpha_gap {U : ℝ} (hU : 22 ≤ U) :
    (3 / 2 * factorialAlpha U - 1) * U + (49 / 50) * factorialAlpha U = 3 / 200 := by
  have hd : (3 / 2 : ℝ) * U + 49 / 50 ≠ 0 := by
    have hp : 0 < (3 / 2 : ℝ) * U + 49 / 50 := by linarith only [hU]
    exact hp.ne'
  have he : factorialAlpha U * ((3 / 2 : ℝ) * U + 49 / 50) = U + 3 / 200 := by
    dsimp only [factorialAlpha]
    exact div_mul_cancel₀ _ hd
  nlinarith only [he]

/-- For `L ≥ 70000` and `1 ≤ b ≤ L`, the factorial logarithmic rounding budget is at most
`L / 70`. The tangent logarithm estimate uniformly controls both the square and linear terms. -/
theorem factorial_log_margin {L b : ℝ} (hL : 70000 ≤ L) (hb : 1 ≤ b) (hbL : b ≤ L) :
    (3 / 2 : ℝ) * (2 * Real.log b) ^ 2 + (49 / 50) * (2 * Real.log b) ≤ L / 70 := by
  have hlogbase : Real.log (70000 : ℝ) < 12 := by
    have h :=
      Real.log_le_log (by norm_num only : (0 : ℝ) < 70000) (by norm_num only : (70000 : ℝ) ≤ 2 ^ 17)
    rw [Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h, Real.log_two_lt_d9]
  have hlog := Real.log_le_log (lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 1) hb) hbL
  have hu0 : 0 ≤ 2 * Real.log b := mul_nonneg (by norm_num only) (Real.log_nonneg hb)
  have hr : (1 : ℝ) ≤ L / 70000 := by linarith only [hL]
  have hrpos : 0 < L / 70000 := by linarith only [hr]
  have hs1 : 1 ≤ Real.sqrt (L / 70000) := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hr
  have ht := Real.log_le_sub_one_of_pos (lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 1) hs1)
  have hslog := Real.log_sqrt hrpos.le
  have he : Real.log L = Real.log (L / 70000) + Real.log 70000 := by
    rw [← Real.log_mul hrpos.ne' (by norm_num only : (70000 : ℝ) ≠ 0)]
    congr 1
    ring
  have hupper : 2 * Real.log b ≤ 20 + 4 * Real.sqrt (L / 70000) := by
    linarith only [hlogbase, hlog, ht, hslog, he]
  have hs2 := Real.sq_sqrt (show 0 ≤ L / 70000 by linarith only [hr])
  have hu2 := pow_le_pow_left₀ hu0 hupper 2
  nlinarith only [hupper, hu2, hs1, hs2, sq_nonneg (Real.sqrt (L / 70000) - 1)]

/-- For `U ≥ 22`, the factorial radius coefficient is strictly below the paired coefficient.
Positive denominators permit an exact rational cross-multiplication. -/
theorem factorialAlpha_lt_paired {U : ℝ} (hU : 22 ≤ U) : factorialAlpha U < pairedAlpha U := by
  have hf : 0 < (3 / 2 : ℝ) * U + 49 / 50 := by linarith only [hU]
  have hp : 0 < (3 / 2 : ℝ) * U + 339 / 500 := by linarith only [hU]
  dsimp only [factorialAlpha, pairedAlpha]
  apply (div_lt_div_iff₀ hf hp).mpr
  nlinarith only [hU]

end PseudoPrime.PrimeTestBounds.MillerRabin
