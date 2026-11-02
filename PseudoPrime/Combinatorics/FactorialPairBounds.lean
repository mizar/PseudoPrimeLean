/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Tactic

/-! # Factorial estimates from paired factors -/

@[expose] public section

namespace PseudoPrime.Combinatorics

/-- For `i < k`, the pair `(i + 1, k - i)` has product at most one quarter
of `(k + 1) ^ 2`. Their sum is `k + 1`; nonnegativity of their squared
difference gives the inequality used in the factorial product estimate. -/
theorem four_mul_pair_le_square (k i : ℕ) (hi : i < k) : 4 * (i + 1) * (k - i) ≤ (k + 1) ^ 2 := by
  have hsub : ((k - i : ℕ) : ℝ) + i = k := by exact_mod_cast Nat.sub_add_cancel (Nat.le_of_lt hi)
  have hs := sq_nonneg (((i : ℝ) + 1) - (k - i : ℕ))
  have hreal : (4 : ℝ) * (i + 1) * (k - i : ℕ) ≤ (k + 1 : ℕ) ^ 2 := by
    norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_pow] at hsub ⊢
    nlinarith only [hsub, hs]
  exact_mod_cast hreal

/-- The product of the reversed factors `k - i` over `i < k` equals `k!`.
Reflect the finite range and use the standard ascending factorial product.
This identifies the second product in the paired factorial estimate. -/
theorem prod_reverse_factorial (k : ℕ) : (∏ i ∈ Finset.range k, (k - i)) = k.factorial := by
  have h := Finset.prod_range_reflect (fun i : ℕ ↦ i + 1) k
  have he : (∏ i ∈ Finset.range k, ((k - 1 - i) + 1 : ℕ)) = ∏ i ∈ Finset.range k, (k - i) := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [Nat.sub_sub, Nat.add_comm 1 i, ← Nat.sub_sub]
    exact Nat.sub_add_cancel (Nat.sub_pos_of_lt (Finset.mem_range.mp hi))
  rw [he, Finset.prod_range_add_one_eq_factorial] at h
  exact h

/-- Pair the ascending and reversed factorial factors to bound the square of
`2 ^ k * k!` by the square of `(k + 1) ^ k`. Multiply the pointwise pair bounds
over the range and identify both factorial products. -/
theorem factorial_pair_square_le (k : ℕ) : (2 ^ k * k.factorial) ^ 2 ≤ ((k + 1) ^ k) ^ 2 := by
  have hprod :
    (∏ i ∈ Finset.range k, 4 * (i + 1) * (k - i)) ≤ ∏ i ∈ Finset.range k, (k + 1) ^ 2 := by
    apply Finset.prod_le_prod
    intro i hi
    exact four_mul_pair_le_square k i (Finset.mem_range.mp hi)
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
    Finset.prod_range_add_one_eq_factorial, prod_reverse_factorial, Finset.prod_const,
    Finset.card_range] at hprod
  have h4 : (4 : ℕ) ^ k = (2 ^ k) ^ 2 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num only, ← pow_mul, Nat.mul_comm 2 k, pow_mul]
  have hk : ((k + 1) ^ 2) ^ k = ((k + 1) ^ k) ^ 2 := by rw [← pow_mul, Nat.mul_comm 2 k, pow_mul]
  rw [h4, hk] at hprod
  nlinarith only [hprod]

/-- For every natural `k`, `2 ^ k * k! ≤ (k + 1) ^ k`. Both sides are
nonnegative, so the paired square bound implies this stronger factorial
estimate. It retains the factor two needed in binomial lower bounds. -/
theorem two_pow_mul_factorial_le (k : ℕ) : 2 ^ k * k.factorial ≤ (k + 1) ^ k := by
  exact (sq_le_sq₀ (Nat.zero_le _) (Nat.zero_le _)).mp (factorial_pair_square_le k)

/-- The binomial coefficient has the paired-factor lower bound without
division: `(2 * (M + 1 - k)) ^ k ≤ (k + 1) ^ k * choose M k`.
Combine the descending-factorial lower bound with the paired factorial
estimate. The natural subtraction makes the statement valid for all `M, k`. -/
theorem paired_choose_power_lower (M k : ℕ) :
    (2 * (M + 1 - k)) ^ k ≤ (k + 1) ^ k * Nat.choose M k := by
  calc
    (2 * (M + 1 - k)) ^ k = 2 ^ k * (M + 1 - k) ^ k := by rw [mul_pow]
    _ ≤ 2 ^ k * M.descFactorial k := Nat.mul_le_mul_left _ (Nat.pow_sub_le_descFactorial M k)
    _ = (2 ^ k * k.factorial) * Nat.choose M k := by
      rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.mul_assoc]
    _ ≤ (k + 1) ^ k * Nat.choose M k := Nat.mul_le_mul_right _ (two_pow_mul_factorial_le k)

/-- The real-valued paired lower bound on `choose M k`. Cast the natural
inequality and divide by the positive power of `k + 1`; the subtraction remains
natural. This is the form used in logarithmic product-count budgets. -/
theorem paired_choose_real_lower (M k : ℕ) :
    (2 * ((M + 1 - k : ℕ) : ℝ) / (k + 1)) ^ k ≤ (Nat.choose M k : ℝ) := by
  have h : ((2 * (M + 1 - k)) ^ k : ℕ) ≤ (k + 1) ^ k * Nat.choose M k :=
    paired_choose_power_lower M k
  have hr : ((2 * (M + 1 - k) : ℕ) : ℝ) ^ k ≤ ((k + 1 : ℕ) : ℝ) ^ k * (Nat.choose M k : ℝ) := by
    exact_mod_cast h
  have hp : 0 < ((k : ℝ) + 1) ^ k := pow_pos (by positivity) _
  rw [div_pow, div_le_iff₀ hp]
  simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one, mul_comm] using hr

end PseudoPrime.Combinatorics
