/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Data.Rat.Cast.Order

/-!
# Fast-converging explicit bounds on `Real.log` of a natural number

This file records a reusable device for bounding `Real.log N` (for a concrete natural `N`) to
high precision with a small number of series terms, using `Real.abs_log_sub_add_sum_range_le`
referenced against the nearest power of two. This is practical even for numbers as large as the
primorials occurring in finite certificate ranges, unlike a linearly-converging tangent-power
technique.
Rational endpoint computation and its Boolean interval check are reflected into
the real Taylor estimate, allowing finite certificates to share the analytic proof.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For positive natural `N` and `x = 1 - N / 2^j` with `|x| < 1`, bound `log N` on both sides
by `j * log 2` minus the first `n` logarithmic series terms, with error
`|x|^(n + 1)/(1 - |x|)`. Rewrite `log (1 - x)` using the power-of-two scale and split mathlib's
absolute-error estimate. Choosing `j` near `log₂ N` gives short high-precision certificates. -/
theorem log_bounds_of_taylor {N : ℕ} (hN : 0 < N) (j n : ℕ) {x : ℝ} (hx : x = 1 - (N : ℝ) / 2 ^ j)
    (hx1 : |x| < 1) :
    (j : ℝ) * Real.log 2 - (∑ i ∈ Finset.range n, x ^ (i + 1) / (i + 1)) -
          |x| ^ (n + 1) / (1 - |x|) ≤
        Real.log N ∧
      Real.log N ≤
        (j : ℝ) * Real.log 2 - (∑ i ∈ Finset.range n, x ^ (i + 1) / (i + 1)) +
          |x| ^ (n + 1) / (1 - |x|) := by
  have h1x : (1 : ℝ) - x = N / 2 ^ j := by
    rw [hx]
    ring
  have hlogeq : Real.log (1 - x) = Real.log N - Real.log ((2 : ℝ) ^ j) := by
    rw [h1x,
      Real.log_div (by exact_mod_cast hN.ne') (pow_ne_zero j (by norm_num only : (2 : ℝ) ≠ 0))]
  have hlog2j : Real.log ((2 : ℝ) ^ j) = (j : ℝ) * Real.log 2 := Real.log_pow 2 j
  have hbound := Real.abs_log_sub_add_sum_range_le hx1 n
  rw [abs_le] at hbound
  constructor
  · linarith only [hbound.1, hlogeq, hlog2j]
  · linarith only [hbound.2, hlogeq, hlog2j]

/--
The same two-sided bound, for a positive real (in practice: rational) reference value `N`
instead of a natural number.  Used to bound `Real.log` of an already-rational upper bound on a
previous application of `PseudoPrime.Analysis.log_bounds_of_taylor`, avoiding the huge
power-of-two denominators that would result from feeding that upper bound directly back into a
second natural-number application.
-/
theorem log_bounds_of_taylor_real {N : ℝ} (hN : 0 < N) (j n : ℕ) {x : ℝ} (hx : x = 1 - N / 2 ^ j)
    (hx1 : |x| < 1) :
    (j : ℝ) * Real.log 2 - (∑ i ∈ Finset.range n, x ^ (i + 1) / (i + 1)) -
          |x| ^ (n + 1) / (1 - |x|) ≤
        Real.log N ∧
      Real.log N ≤
        (j : ℝ) * Real.log 2 - (∑ i ∈ Finset.range n, x ^ (i + 1) / (i + 1)) +
          |x| ^ (n + 1) / (1 - |x|) := by
  have h1x : (1 : ℝ) - x = N / 2 ^ j := by
    rw [hx]
    ring
  have hlogeq : Real.log (1 - x) = Real.log N - Real.log ((2 : ℝ) ^ j) := by
    rw [h1x, Real.log_div hN.ne' (pow_ne_zero j (by norm_num only : (2 : ℝ) ≠ 0))]
  have hlog2j : Real.log ((2 : ℝ) ^ j) = (j : ℝ) * Real.log 2 := Real.log_pow 2 j
  have hbound := Real.abs_log_sub_add_sum_range_le hx1 n
  rw [abs_le] at hbound
  constructor
  · linarith only [hbound.1, hlogeq, hlog2j]
  · linarith only [hbound.2, hlogeq, hlog2j]

/-- The first `n` terms of the logarithmic series in rational arithmetic:
`sum i<n, x^(i+1)/(i+1)`. The input is the rational displacement from a nearby
power of two. This finite computation is used by kernel-checked log intervals. -/
def rationalLogSeries (x : ℚ) (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range n, x ^ (i + 1) / (i + 1)

/-- The rational Taylor error `abs(x)^(n+1)/(1-abs(x))`. For `abs(x)<1`
this bounds the remainder after `n` logarithmic series terms. The interval
checker verifies the displacement condition before this value is used. -/
def rationalLogRemainder (x : ℚ) (n : ℕ) : ℚ :=
  |x| ^ (n + 1) / (1 - |x|)

/-- A rational lower endpoint for `log N`, using `j` times the certified
lower logarithm of two minus the Taylor series and remainder at `1-N/2^j`.
It is a valid bound when `N>0` and the displacement has absolute value below
one. This gives the computable lower endpoint of a logarithm certificate. -/
def rationalLogLower (N : ℚ) (j n : ℕ) : ℚ :=
  (j : ℚ) * (6931471803 / 10000000000) - rationalLogSeries (1 - N / 2 ^ j) n -
    rationalLogRemainder (1 - N / 2 ^ j) n

/-- A rational upper endpoint for `log N`, using `j` times the certified
upper logarithm of two minus the Taylor series plus its remainder at `1-N/2^j`.
Positive `N` and displacement of absolute value below one make this a valid
upper bound. This gives the computable upper endpoint of a logarithm certificate. -/
def rationalLogUpper (N : ℚ) (j n : ℕ) : ℚ :=
  (j : ℚ) * (6931471808 / 10000000000) - rationalLogSeries (1 - N / 2 ^ j) n +
    rationalLogRemainder (1 - N / 2 ^ j) n

/-- Casting the rational Taylor sum to the reals gives the real Taylor sum.
Use the rational ring homomorphism to commute casting with the finite sum,
powers and division. This connects rational computation to the analytic estimate. -/
theorem rationalLogSeries_cast (x : ℚ) (n : ℕ) :
    (rationalLogSeries x n : ℝ) = ∑ i ∈ Finset.range n, (x : ℝ) ^ (i + 1) / (i + 1) := by
  change (Rat.castHom ℝ) (∑ i ∈ Finset.range n, x ^ (i + 1) / (i + 1)) = _
  rw [map_sum]
  simp only [Rat.coe_castHom, Rat.cast_div, Rat.cast_pow, Rat.cast_add, Rat.cast_natCast,
    Rat.cast_one]

/-- For positive rational `N` whose power-of-two displacement has absolute
value below one, the rational endpoints enclose its real logarithm. Apply the
real Taylor estimate and the certified logarithm of two, then commute rational
casts with arithmetic. This proves the mathematical meaning of both endpoints. -/
theorem rationalLogBounds_sound {N : ℚ} (hN : 0 < N) (j n : ℕ) (hx : |1 - N / 2 ^ j| < 1) :
    (rationalLogLower N j n : ℝ) ≤ Real.log (N : ℝ) ∧
      Real.log (N : ℝ) ≤ (rationalLogUpper N j n : ℝ) := by
  have hxR : |1 - (N : ℝ) / 2 ^ j| < 1 := by
    have h := (Rat.cast_lt (K := ℝ)).mpr hx
    simpa only [Rat.cast_abs, Rat.cast_sub, Rat.cast_one, Rat.cast_div, Rat.cast_pow,
      Rat.cast_ofNat] using h
  have ht :=
    log_bounds_of_taylor_real ((Rat.cast_pos (K := ℝ)).mpr hN) j n (x := 1 - (N : ℝ) / 2 ^ j) rfl
      hxR
  have h2l : (6931471803 / 10000000000 : ℝ) ≤ Real.log 2 := by linarith only [Real.log_two_gt_d9]
  have h2u : Real.log 2 ≤ (6931471808 / 10000000000 : ℝ) := by linarith only [Real.log_two_lt_d9]
  have hl := mul_le_mul_of_nonneg_left h2l (Nat.cast_nonneg j : (0 : ℝ) ≤ j)
  have hu := mul_le_mul_of_nonneg_left h2u (Nat.cast_nonneg j : (0 : ℝ) ≤ j)
  simp only [rationalLogLower, rationalLogUpper, Rat.cast_add, Rat.cast_sub, Rat.cast_mul,
    Rat.cast_natCast, Rat.cast_div, Rat.cast_ofNat, rationalLogSeries_cast, rationalLogRemainder,
    Rat.cast_pow, Rat.cast_abs, Rat.cast_one]
  constructor <;> linarith only [ht.1, ht.2, hl, hu]

/-- Check positivity, the Taylor displacement condition, and containment
of the computed endpoints in the proposed rational interval `[lo,hi]`.
The arguments specify `N`, its power-of-two scale `j`, and the number of series
terms `n`. A true result certifies the real logarithm interval in the kernel. -/
def rationalLogIntervalCheck (N : ℚ) (j n : ℕ) (lo hi : ℚ) : Bool :=
  decide (0 < N ∧ |1 - N / 2 ^ j| < 1 ∧ lo ≤ rationalLogLower N j n ∧ rationalLogUpper N j n ≤ hi)

/-- A successful rational interval check implies that `log N` lies between
the proposed real endpoints. Extract the finite rational comparisons, use the
Taylor endpoint theorem and preserve order under casting. This reflects a
computable certificate into the logarithm bounds used by analytic comparisons. -/
theorem rationalLogIntervalCheck_sound {N lo hi : ℚ} {j n : ℕ}
    (h : rationalLogIntervalCheck N j n lo hi = true) :
    (lo : ℝ) ≤ Real.log (N : ℝ) ∧ Real.log (N : ℝ) ≤ (hi : ℝ) := by
  have hc :
    0 < N ∧ |1 - N / 2 ^ j| < 1 ∧ lo ≤ rationalLogLower N j n ∧ rationalLogUpper N j n ≤ hi :=
    of_decide_eq_true h
  have ht := rationalLogBounds_sound hc.1 j n hc.2.1
  exact
    ⟨((Rat.cast_le (K := ℝ)).mpr hc.2.2.1).trans ht.1,
      ht.2.trans ((Rat.cast_le (K := ℝ)).mpr hc.2.2.2)⟩

end PseudoPrime.Analysis
