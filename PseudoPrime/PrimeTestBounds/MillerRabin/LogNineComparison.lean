/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Tactic

/-! # Comparison with the base-nine logarithm -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For `L ≥ log 9`, the coefficient `517/1250` max bound is at most
`2 * (L / log 9)²`. A certified upper bound for `log 3` controls the coefficient,
and the lower bound on `L` controls the constant branch. This supplies the
base-nine corollary once the max-form witness theorem is proved. -/
theorem max_04136_le_log_nine_sq {L : ℝ} (hL : Real.log 9 ≤ L) :
    max 2 ((517 / 1250 : ℝ) * L ^ 2) ≤ 2 * (L / Real.log 9) ^ 2 := by
  have hlog : Real.log (9 : ℝ) = 2 * Real.log 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num only, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
  have hpos : 0 < Real.log (9 : ℝ) := Real.log_pos (by norm_num only)
  have hupper : Real.log (9 : ℝ) < 2198 / 1000 := by linarith only [hlog, Real.log_three_lt_d9]
  have hsquare : (517 / 1250 : ℝ) * (Real.log 9) ^ 2 ≤ 2 := by
    nlinarith only [hpos, hupper, sq_nonneg (Real.log 9 - 2198 / 1000)]
  have hratio : 1 ≤ L / Real.log 9 := (le_div_iff₀ hpos).mpr (by linarith only [hL])
  have hs : (517 / 1250 : ℝ) * L ^ 2 ≤ 2 * (L / Real.log 9) ^ 2 := by
    rw [div_pow, ← mul_div_assoc]
    apply (le_div_iff₀ (sq_pos_of_pos hpos)).mpr
    have hmul := mul_nonneg (sub_nonneg.mpr hsquare) (sq_nonneg L)
    nlinarith only [hmul]
  apply max_le
  · nlinarith only [hratio]
  · exact hs

/-- For `x ≥ 9`, the max-form bound with coefficient `517/1250` is at most
`2 * (logb 9 x)²`. Apply monotonicity of the logarithm and the preceding
comparison. This transfers a max-form Miller–Rabin bound to the base-nine form. -/
theorem max_04136_le_logb_nine_sq {x : ℝ} (hx : 9 ≤ x) :
    max 2 ((517 / 1250 : ℝ) * (Real.log x) ^ 2) ≤ 2 * (Real.logb 9 x) ^ 2 := by
  exact max_04136_le_log_nine_sq (Real.log_le_log (by norm_num only) hx)

end PseudoPrime.PrimeTestBounds.MillerRabin
