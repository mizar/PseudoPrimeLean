/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.LogTaylorBounds

/-! # Higher-precision rational logarithm certificates -/

@[expose] public section

namespace PseudoPrime.Analysis

set_option maxRecDepth 8192 in
/-- The logarithm of two lies in the displayed rational interval of width
`10⁻¹⁵`. A 64-term Taylor certificate for `log (1/2)` and `log_inv` provide
the bound without floating-point computation. These bounds support rational
logarithm certificates whose required precision exceeds the coarse constants. -/
theorem log_two_precise_bounds :
    (693147180559945 / 1000000000000000 : ℝ) ≤ Real.log 2 ∧
      Real.log 2 ≤ (693147180559946 / 1000000000000000 : ℝ) := by
  have hc :
    rationalLogIntervalCheck (1 / 2) 0 64 (-693147180559946 / 1000000000000000)
        (-693147180559945 / 1000000000000000) =
      true := by
    decide +kernel
  have h := rationalLogIntervalCheck_sound hc
  norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_neg, Rat.cast_ofNat] at h
  rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num only, Real.log_inv] at h
  constructor
  · linarith only [h.2]
  · linarith only [h.1]

/-- The refined rational lower endpoint for `log N` at binary scale `j` and
Taylor length `n`. It combines the precise lower bound for `log 2` with the
existing Taylor sum and remainder. The associated soundness theorem requires
positive `N` and a displacement of absolute value below one. -/
def preciseLogLower (N : ℚ) (j n : ℕ) : ℚ :=
  (j : ℚ) * (693147180559945 / 1000000000000000) - rationalLogSeries (1 - N / 2 ^ j) n -
    rationalLogRemainder (1 - N / 2 ^ j) n

/-- The refined rational upper endpoint for `log N` at binary scale `j` and
Taylor length `n`. It combines the precise upper bound for `log 2` with the
existing Taylor sum and remainder. The associated soundness theorem requires
positive `N` and a displacement of absolute value below one. -/
def preciseLogUpper (N : ℚ) (j n : ℕ) : ℚ :=
  (j : ℚ) * (693147180559946 / 1000000000000000) - rationalLogSeries (1 - N / 2 ^ j) n +
    rationalLogRemainder (1 - N / 2 ^ j) n

/-- For positive rational `N` with convergent binary-scale Taylor displacement,
the refined endpoints enclose the real logarithm. Combine the existing Taylor
estimate with the kernel-certified `log 2` interval and cast rational terms.
This is the analytic soundness result for the refined interval checker. -/
theorem preciseLog_bounds {N : ℚ} (hN : 0 < N) (j n : ℕ) (hx : |1 - N / 2 ^ j| < 1) :
    (preciseLogLower N j n : ℝ) ≤ Real.log (N : ℝ) ∧
      Real.log (N : ℝ) ≤ (preciseLogUpper N j n : ℝ) := by
  have hxR : |1 - (N : ℝ) / 2 ^ j| < 1 := by
    have h := (Rat.cast_lt (K := ℝ)).mpr hx
    simpa only [Rat.cast_abs, Rat.cast_sub, Rat.cast_one, Rat.cast_div, Rat.cast_pow,
      Rat.cast_ofNat] using h
  have ht :=
    log_bounds_of_taylor_real ((Rat.cast_pos (K := ℝ)).mpr hN) j n (x := 1 - (N : ℝ) / 2 ^ j) rfl
      hxR
  have hl := mul_le_mul_of_nonneg_left log_two_precise_bounds.1 (Nat.cast_nonneg j : (0 : ℝ) ≤ j)
  have hu := mul_le_mul_of_nonneg_left log_two_precise_bounds.2 (Nat.cast_nonneg j : (0 : ℝ) ≤ j)
  simp only [preciseLogLower, preciseLogUpper, Rat.cast_add, Rat.cast_sub, Rat.cast_mul,
    Rat.cast_natCast, Rat.cast_div, Rat.cast_ofNat, rationalLogSeries_cast, rationalLogRemainder,
    Rat.cast_pow, Rat.cast_abs, Rat.cast_one]
  constructor
  · linarith only [ht.1, ht.2, hl, hu]
  · linarith only [ht.1, ht.2, hl, hu]

/-- Check rational lower and upper endpoints for the logarithm of `N` at the
given binary scale and Taylor length. The Boolean also checks positivity and
the convergence condition; its soundness theorem supplies the real interval. -/
def preciseLogCheck (N : ℚ) (j n : ℕ) (lo hi : ℚ) : Bool :=
  decide (0 < N ∧ |1 - N / 2 ^ j| < 1 ∧ lo ≤ preciseLogLower N j n ∧ preciseLogUpper N j n ≤ hi)

/-- A successful refined rational interval check encloses the real logarithm.
Extract the checked hypotheses, apply the Taylor enclosure and cast the endpoint
inequalities. This transfers computed certificates to later analytic arguments. -/
theorem preciseLogCheck_sound {N lo hi : ℚ} {j n : ℕ} (h : preciseLogCheck N j n lo hi = true) :
    (lo : ℝ) ≤ Real.log (N : ℝ) ∧ Real.log (N : ℝ) ≤ (hi : ℝ) := by
  have hc : 0 < N ∧ |1 - N / 2 ^ j| < 1 ∧ lo ≤ preciseLogLower N j n ∧ preciseLogUpper N j n ≤ hi :=
    of_decide_eq_true h
  have ht := preciseLog_bounds hc.1 j n hc.2.1
  exact
    ⟨((Rat.cast_le (K := ℝ)).mpr hc.2.2.1).trans ht.1,
      ht.2.trans ((Rat.cast_le (K := ℝ)).mpr hc.2.2.2)⟩

end PseudoPrime.Analysis
