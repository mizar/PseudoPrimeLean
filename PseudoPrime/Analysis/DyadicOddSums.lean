/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Algebra.BigOperators.Ring.Finset

/-! # Dyadic sums split into even and odd terms -/

public section

namespace PseudoPrime.Analysis

/-- Split a finite sum of twice the length into its even and odd terms.
The identity holds in any additive commutative monoid and is proved by induction on the length.
It provides the reindexing step for compressed dyadic finite sums. -/
theorem sum_range_even_odd {R : Type*} [AddCommMonoid R] (f : ℕ → R) (n : ℕ) :
    (∑ k ∈ Finset.range (2 * n), f k) =
      (∑ k ∈ Finset.range n, f (2 * k)) + ∑ k ∈ Finset.range n, f (2 * k + 1) := by
  induction n with
  | zero => simp only [Nat.mul_zero, Finset.range_zero, Finset.sum_empty, add_zero]
  | succ n
    ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ, Finset.sum_range_succ]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.add_zero]
    ac_rfl

/-- Express a dyadic sum using its odd terms and the preceding dyadic sum.
The hypothesis supplies the value of each even term, including the term at zero.
Splitting the range and factoring the common multiplier gives the recurrence used by the
compressed finite zeta sum. -/
theorem sum_range_pow_two_odd {R : Type*} [Semiring R] (f : ℕ → R) (q : R)
    (h : ∀ k, f (2 * k) = q * f k) (n : ℕ) :
    (∑ k ∈ Finset.range (2 ^ (n + 1)), f k) =
      (∑ k ∈ Finset.range (2 ^ n), f (2 * k + 1)) + q * ∑ k ∈ Finset.range (2 ^ n), f k := by
  rw [pow_succ, mul_comm (2 ^ n), sum_range_even_odd, Finset.mul_sum, add_comm]
  congr 1
  exact Finset.sum_congr rfl (fun k _ ↦ h k)

/-- Doubling an odd-index prefix appends the next equally long block of odd terms.
The identity follows from the finite-sum range decomposition and holds in any additive
commutative monoid. It permits successive odd sums to share one cumulative computation. -/
theorem odd_prefix_succ {R : Type*} [AddCommMonoid R] (f : ℕ → R) (m : ℕ) :
    (∑ k ∈ Finset.range (2 ^ (m + 1)), f (2 * k + 1)) =
      (∑ k ∈ Finset.range (2 ^ m), f (2 * k + 1)) +
        ∑ k ∈ Finset.range (2 ^ m), f (2 * (2 ^ m + k) + 1) := by
  rw [pow_succ, mul_comm (2 ^ m), two_mul, Finset.sum_range_add]

end PseudoPrime.Analysis
