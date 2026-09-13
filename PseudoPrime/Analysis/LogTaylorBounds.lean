/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Fast-converging explicit bounds on `Real.log` of a natural number

This file records a reusable device for bounding `Real.log N` (for a concrete natural `N`) to
high precision with a small number of series terms, using `Real.abs_log_sub_add_sum_range_le`
referenced against the nearest power of two. This is practical even for numbers as large as the
primorials occurring in finite certificate ranges, unlike a linearly-converging tangent-power
technique.
-/

namespace PseudoPrime.Analysis

/-- The two-sided explicit bound on `Real.log N` from the log Taylor series at `1 - N / 2^j`. -/
theorem log_bounds_of_taylor {N : ℕ} (hN : 0 < N) (j n : ℕ) {x : ℝ} (hx : x = 1 - (N : ℝ) / 2 ^ j)
    (hx1 : |x| < 1) :
    (j : ℝ) * Real.log 2 - (∑ i ∈ Finset.range n, x ^ (i + 1) / (i + 1)) -
          |x| ^ (n + 1) / (1 - |x|) ≤
        Real.log N ∧
      Real.log N ≤
        (j : ℝ) * Real.log 2 - (∑ i ∈ Finset.range n, x ^ (i + 1) / (i + 1)) +
          |x| ^ (n + 1) / (1 - |x|) := by
  have h1x : (1 : ℝ) - x = N / 2 ^ j := by
    rw [hx]; ring
  have hlogeq : Real.log (1 - x) = Real.log N - Real.log ((2 : ℝ) ^ j) := by
    rw [h1x, Real.log_div (by exact_mod_cast hN.ne') (by positivity)]
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
    rw [hx]; ring
  have hlogeq : Real.log (1 - x) = Real.log N - Real.log ((2 : ℝ) ^ j) := by
    rw [h1x, Real.log_div hN.ne' (by positivity)]
  have hlog2j : Real.log ((2 : ℝ) ^ j) = (j : ℝ) * Real.log 2 := Real.log_pow 2 j
  have hbound := Real.abs_log_sub_add_sum_range_le hx1 n
  rw [abs_le] at hbound
  constructor
  · linarith only [hbound.1, hlogeq, hlog2j]
  · linarith only [hbound.2, hlogeq, hlog2j]

end PseudoPrime.Analysis
