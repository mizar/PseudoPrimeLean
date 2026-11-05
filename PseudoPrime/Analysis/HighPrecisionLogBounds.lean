/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.PreciseLogTaylorBounds

/-!
# Rational bounds for logarithms

The Taylor bounds in this file accept independently certified bounds for `log 2`.  They allow
finite arithmetic certificates to use more precision without changing the analytic argument.
-/

@[expose] public section

namespace PseudoPrime.Analysis

set_option maxRecDepth 16384 in
/-- A 27-decimal rational interval for `log 2`, certified by the Taylor interval checker. -/
theorem log_two_27_bounds :
    (693147180559945309417232121 / 1000000000000000000000000000 : ℝ) ≤ Real.log 2 ∧
      Real.log 2 ≤ (693147180559945309417232122 / 1000000000000000000000000000 : ℝ) := by
  have hc :
    rationalLogIntervalCheck (1 / 2) 0 128
        (-693147180559945309417232122 / 1000000000000000000000000000)
        (-693147180559945309417232121 / 1000000000000000000000000000) =
      true := by
    decide +kernel
  have h := rationalLogIntervalCheck_sound hc
  norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_neg, Rat.cast_ofNat] at h
  rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num only, Real.log_inv] at h
  constructor
  · linarith only [h.2]
  · linarith only [h.1]

/-- Lower Taylor approximation to `log N`, using the supplied lower bound for `log 2`. -/
def scaledLogLower (N : ℚ) (j n : ℕ) (lo2 : ℚ) : ℚ :=
  (j : ℚ) * lo2 - rationalLogSeries (1 - N / 2 ^ j) n - rationalLogRemainder (1 - N / 2 ^ j) n

/-- Upper Taylor approximation to `log N`, using the supplied upper bound for `log 2`. -/
def scaledLogUpper (N : ℚ) (j n : ℕ) (hi2 : ℚ) : ℚ :=
  (j : ℚ) * hi2 - rationalLogSeries (1 - N / 2 ^ j) n + rationalLogRemainder (1 - N / 2 ^ j) n

/-- Positive rational inputs in the Taylor domain satisfy the parameterized logarithm bounds.
The proof substitutes the supplied bounds for `log 2` into the real Taylor estimate. -/
theorem scaledLog_bounds {N lo2 hi2 : ℚ} (hN : 0 < N) (j n : ℕ) (hx : |1 - N / 2 ^ j| < 1)
    (hl2 : (lo2 : ℝ) ≤ Real.log 2) (hu2 : Real.log 2 ≤ (hi2 : ℝ)) :
    (scaledLogLower N j n lo2 : ℝ) ≤ Real.log (N : ℝ) ∧
      Real.log (N : ℝ) ≤ (scaledLogUpper N j n hi2 : ℝ) := by
  have hxR : |1 - (N : ℝ) / 2 ^ j| < 1 := by
    have h := (Rat.cast_lt (K := ℝ)).mpr hx
    simpa only [Rat.cast_abs, Rat.cast_sub, Rat.cast_one, Rat.cast_div, Rat.cast_pow,
      Rat.cast_ofNat] using h
  have ht :=
    log_bounds_of_taylor_real ((Rat.cast_pos (K := ℝ)).mpr hN) j n (x := 1 - (N : ℝ) / 2 ^ j) rfl
      hxR
  have hl := mul_le_mul_of_nonneg_left hl2 (Nat.cast_nonneg j : (0 : ℝ) ≤ j)
  have hu := mul_le_mul_of_nonneg_left hu2 (Nat.cast_nonneg j : (0 : ℝ) ≤ j)
  simp only [scaledLogLower, scaledLogUpper, Rat.cast_add, Rat.cast_sub, Rat.cast_mul,
    Rat.cast_natCast, Rat.cast_div, Rat.cast_ofNat, rationalLogSeries_cast, rationalLogRemainder,
    Rat.cast_pow, Rat.cast_abs, Rat.cast_one]
  constructor
  · linarith only [ht.1, ht.2, hl, hu]
  · linarith only [ht.1, ht.2, hl, hu]

/-- Check a logarithm interval using the 27-decimal bound for `log 2`. Positivity and Taylor
convergence are checked along with the rational endpoints. -/
def fineLogCheck (N : ℚ) (j n : ℕ) (lo hi : ℚ) : Bool :=
  decide
    (0 < N ∧
      |1 - N / 2 ^ j| < 1 ∧
      lo ≤ scaledLogLower N j n (693147180559945309417232121 / 1000000000000000000000000000) ∧
      scaledLogUpper N j n (693147180559945309417232122 / 1000000000000000000000000000) ≤ hi)

/-- A successful fine logarithm check encloses the real logarithm. Cast the verified rational
inequalities and apply the parameterized Taylor bound to transfer a finite certificate. -/
theorem fineLogCheck_sound {N lo hi : ℚ} {j n : ℕ} (h : fineLogCheck N j n lo hi = true) :
    (lo : ℝ) ≤ Real.log (N : ℝ) ∧ Real.log (N : ℝ) ≤ (hi : ℝ) := by
  have hc :
    0 < N ∧
      |1 - N / 2 ^ j| < 1 ∧
      lo ≤ scaledLogLower N j n (693147180559945309417232121 / 1000000000000000000000000000) ∧
      scaledLogUpper N j n (693147180559945309417232122 / 1000000000000000000000000000) ≤ hi :=
    of_decide_eq_true h
  have h2l :
    ((693147180559945309417232121 / 1000000000000000000000000000 : ℚ) : ℝ) ≤ Real.log 2 := by
    norm_num only [Rat.cast_div, Rat.cast_ofNat]
    exact log_two_27_bounds.1
  have h2u :
    Real.log 2 ≤ ((693147180559945309417232122 / 1000000000000000000000000000 : ℚ) : ℝ) := by
    norm_num only [Rat.cast_div, Rat.cast_ofNat]
    linarith only [log_two_27_bounds.2]
  have ht := scaledLog_bounds hc.1 j n hc.2.1 h2l h2u
  exact
    ⟨((Rat.cast_le (K := ℝ)).mpr hc.2.2.1).trans ht.1,
      ht.2.trans ((Rat.cast_le (K := ℝ)).mpr hc.2.2.2)⟩

end PseudoPrime.Analysis
