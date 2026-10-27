/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Algebra.BigOperators.Intervals

/-! # Summation and property transfer over equal natural interval blocks -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For any additive commutative monoid, sum over equal half-open natural
blocks equals the sum over their combined interval. Induct on the block count and
use adjacent interval summation. This joins compact arithmetic block certificates. -/
theorem sum_Ico_equal_blocks {M : Type*} [AddCommMonoid M] (f : ℕ → M) (d k : ℕ) :
    (∑ i ∈ Finset.range k, ∑ n ∈ Finset.Ico (d * i) (d * (i + 1)), f n) =
      ∑ n ∈ Finset.Ico 0 (d * k), f n := by
  induction k with
  | zero => simp only [Finset.sum_range_zero, Nat.mul_zero, Finset.Ico_self, Finset.sum_empty]
  | succ k ih =>
    rw [Finset.sum_range_succ, ih,
      Finset.sum_Ico_consecutive f (Nat.zero_le _) (Nat.mul_le_mul_left d (Nat.le_succ k))]

/-- For any additive commutative monoid, sum over equal right-closed natural
blocks equals the sum over their combined interval. Join adjacent blocks inductively. -/
theorem sum_Ioc_equal_blocks {M : Type*} [AddCommMonoid M] (f : ℕ → M) (d k : ℕ) :
    (∑ i ∈ Finset.range k, ∑ n ∈ Finset.Ioc (d * i) (d * (i + 1)), f n) =
      ∑ n ∈ Finset.Ioc 0 (d * k), f n := by
  induction k with
  | zero => simp only [Finset.sum_range_zero, Nat.mul_zero, Finset.Ioc_self, Finset.sum_empty]
  | succ k ih =>
    rw [Finset.sum_range_succ, ih,
      Finset.sum_Ioc_consecutive f (Nat.zero_le _) (Nat.mul_le_mul_left d (Nat.le_succ k))]

/-- A property checked on each positive-width natural block holds on the
combined half-open interval. Assign each index to its quotient block; division inequalities
prove membership. This transfers local numerical checks without re-enumerating the full range. -/
theorem forall_Ico_of_equal_blocks {P : ℕ → Prop} {d k : ℕ} (hd : 0 < d)
    (hc : ∀ i < k, ∀ n ∈ Finset.Ico (d * i) (d * (i + 1)), P n) :
    ∀ n ∈ Finset.Ico 0 (d * k), P n := by
  intro n hn
  have hi : n / d < k :=
    (Nat.div_lt_iff_lt_mul hd).mpr (by simpa only [Nat.mul_comm] using (Finset.mem_Ico.mp hn).2)
  have hl : d * (n / d) ≤ n := by simpa only [Nat.mul_comm] using Nat.div_mul_le_self n d
  exact hc (n / d) hi n (Finset.mem_Ico.mpr ⟨hl, Nat.lt_mul_div_succ n hd⟩)

end PseudoPrime.Analysis
