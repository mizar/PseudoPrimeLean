/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-! # Common Euler coefficient in section 137 -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For a trace deficit between zero and four, the signed combination of the main
weight and the Euler weight loses at most four times the negative part of their sum.
When the combined profile is nonnegative this gives (137.6). -/
theorem common_euler_lower {a : ℝ} (ha : 0 ≤ a) (hb : a ≤ 4) (f g : ℝ) :
    -4 * g - 4 * max 0 (-(f + g)) ≤ (4 - a) * f - a * g := by
  by_cases h : 0 ≤ f + g
  · rw [max_eq_left (neg_nonpos.mpr h)]
    linarith only [mul_nonneg (sub_nonneg.mpr hb) h]
  · rw [max_eq_right (neg_nonneg.mpr (le_of_not_ge h))]
    linarith only [mul_nonpos_of_nonneg_of_nonpos ha (le_of_not_ge h)]

/-- In a finite weighted Euler sum, retain the full combined weight at indices where
the deficit is known to vanish. On the complement, charge only the negative part
of the combined weight. This gives the finite truncations of (137.7). -/
theorem common_euler_sum_lower (s k : Finset ℕ) (w a f g : ℕ → ℝ) (hw : ∀ n ∈ s, 0 ≤ w n)
    (ha : ∀ n ∈ s, a n ∈ Set.Icc 0 4) (hk : ∀ n ∈ k, a n = 0) :
    ∑ n ∈ s, w n * (-4 * g n + if n ∈ k then 4 * (f n + g n) else -(4 * max 0 (-(f n + g n)))) ≤
      ∑ n ∈ s, w n * ((4 - a n) * f n - a n * g n) := by
  apply Finset.sum_le_sum
  intro n hn
  apply mul_le_mul_of_nonneg_left _ (hw n hn)
  by_cases h : n ∈ k
  · rw [ite_eq_left h, hk n h]
    linarith only
  · rw [ite_eq_right h, ← sub_eq_add_neg]
    exact common_euler_lower (ha n hn).1 (ha n hn).2 _ _

end PseudoPrime.PrimeTestBounds.MillerRabin
