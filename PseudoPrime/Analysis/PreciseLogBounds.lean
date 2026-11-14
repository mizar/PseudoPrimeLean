/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.PreciseLogArithmetic
import PseudoPrime.Analysis.LogTwoPrecise

/-! # Soundness of precise rational logarithm intervals -/

public section

namespace PseudoPrime.Analysis

/-- For positive rational `N` with a convergent reduced Taylor series, the precise rational
endpoints bound `log N`. The log-two enclosure is proved internally and substituted into the
standard real Taylor bound. -/
theorem rational_precise_log_bounds {N : ℚ} (hN : 0 < N) (j n : ℕ) (hx : |1 - N / 2 ^ j| < 1) :
    (rationalPreciseLogLower N j n : ℝ) ≤ Real.log (N : ℝ) ∧
      Real.log (N : ℝ) ≤ (rationalPreciseLogUpper N j n : ℝ) := by
  have hxR : |1 - (N : ℝ) / 2 ^ j| < 1 := by
    have h := (Rat.cast_lt (K := ℝ)).mpr hx
    simpa only [Rat.cast_abs, Rat.cast_sub, Rat.cast_one, Rat.cast_div, Rat.cast_pow,
      Rat.cast_ofNat] using h
  have ht :=
    log_bounds_of_taylor_real ((Rat.cast_pos (K := ℝ)).mpr hN) j n (x := 1 - (N : ℝ) / 2 ^ j) rfl
      hxR
  have hl := mul_le_mul_of_nonneg_left log_two_precise.1 (Nat.cast_nonneg j : (0 : ℝ) ≤ j)
  have hu := mul_le_mul_of_nonneg_left log_two_precise.2 (Nat.cast_nonneg j : (0 : ℝ) ≤ j)
  simp only [rationalPreciseLogLower, rationalPreciseLogUpper, Rat.cast_add, Rat.cast_sub,
    Rat.cast_mul, Rat.cast_natCast, Rat.cast_div, Rat.cast_ofNat, rationalLogSeries_cast,
    rationalLogRemainder, Rat.cast_pow, Rat.cast_abs, Rat.cast_one]
  constructor <;> linarith only [ht.1, ht.2, hl, hu]

/-- A successful precise rational logarithm check implies the corresponding two-sided real
logarithm bound. This is the soundness interface for kernel-checked endpoint certificates. -/
theorem rational_precise_log_check_sound {N lo hi : ℚ} {j n : ℕ}
    (h : rationalPreciseLogCheck N j n lo hi = true) :
    (lo : ℝ) ≤ Real.log (N : ℝ) ∧ Real.log (N : ℝ) ≤ (hi : ℝ) := by
  have hc :
    0 < N ∧
      |1 - N / 2 ^ j| < 1 ∧
      lo ≤ rationalPreciseLogLower N j n ∧ rationalPreciseLogUpper N j n ≤ hi :=
    of_decide_eq_true h
  have ht := rational_precise_log_bounds hc.1 j n hc.2.1
  exact
    ⟨((Rat.cast_le (K := ℝ)).mpr hc.2.2.1).trans ht.1,
      ht.2.trans ((Rat.cast_le (K := ℝ)).mpr hc.2.2.2)⟩

end PseudoPrime.Analysis
