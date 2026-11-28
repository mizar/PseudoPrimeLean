/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterRecoveryAbel644
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterReflected570
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterReflected570

/-! # Section 122 transfer of the six reflected prefix moments -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The section 122 reflected Mangoldt moment at exponent 157/100 and logarithmic degree j. -/
noncomputable def reflectedMoment644 (j n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n * Real.log n ^ j * (n : ℝ) ^ (-(157 / 100 : ℝ))

/-- A positive exponential Taylor minorant compares each shifted-weight term to finitely
many certified moments at exponent 79/50. -/
private theorem moment_taylor {n : ℕ} (hn : 0 < n) (j m : ℕ) :
    ∑ k ∈ Finset.range m, (1 / 100 : ℝ) ^ k / k.factorial * quarterMangoldtMoment (j + k) n ≤
      reflectedMoment644 j n := by
  have hx : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have he :
    (n : ℝ) ^ (-(79 / 50 : ℝ)) * Real.exp (Real.log n * (1 / 100)) =
      (n : ℝ) ^ (-(157 / 100 : ℝ)) := by
    rw [Real.rpow_def_of_pos hx, Real.rpow_def_of_pos hx, ← Real.exp_add]
    congr 1
    ring
  have ht :=
    Real.sum_le_exp_of_nonneg
      (mul_nonneg (Real.log_natCast_nonneg n) (by norm_num only : (0 : ℝ) ≤ 1 / 100)) m
  have hm := mul_le_mul_of_nonneg_left ht (quarter_mangoldt_moment_nonneg j n)
  rw [Finset.mul_sum] at hm
  unfold reflectedMoment644
  rw [← he, ← mul_assoc]
  apply le_trans (Finset.sum_le_sum (fun k _ ↦ le_of_eq ?_)) hm
  unfold quarterMangoldtMoment
  rw [pow_add, mul_pow]
  ring

/-- The improved finite moment bound obtained by Taylor expansion through degree five. -/
noncomputable def reflectedFloor644 (j : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (6 - j), (1 / 100 : ℝ) ^ k / k.factorial * momentFloor570 (j + k)

/-- For degrees up to five, summation of the Taylor minorant gives the improved lower bound. -/
theorem reflected_moment_lower_644 (j : ℕ) (hj : j ≤ 5) :
    reflectedFloor644 j ≤ ∑ n ∈ Finset.Ioc 0 2701, reflectedMoment644 j n := by
  have ht :=
    Finset.sum_le_sum (s := Finset.Ioc 0 2701)
      (fun n hn ↦ moment_taylor (Finset.mem_Ioc.mp hn).1 j (6 - j))
  rw [Finset.sum_comm] at ht
  simp only [← Finset.mul_sum] at ht
  apply le_trans (Finset.sum_le_sum (fun k hk ↦ ?_)) ht
  have hk' := Finset.mem_range.mp hk
  have he := Nat.sub_add_cancel (Nat.le_trans hj (by decide : 5 ≤ 6))
  have hdeg : j + k ≤ 5 := by linarith only [hk', he]
  exact mul_le_mul_of_nonneg_left (moment_floor (j + k) hdeg) (by positivity)

/-- Binomial expansion of a shifted reflected summand in six log moments. -/
theorem reflected_expand_644 (z : ℝ) (n : ℕ) :
    ArithmeticFunction.vonMangoldt n * quarterReflectedWeight z n =
      ∑ j ∈ Finset.range 6, (Nat.choose 5 j : ℝ) * z ^ (5 - j) * reflectedMoment644 j n := by
  unfold quarterReflectedWeight reflectedMoment644
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, Nat.reduceSub,
    Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero]
  ring

/-- The shifted logarithm expands the section 122 prefix into the six
power-log moments. The nonnegative binomial factors preserve the lower bounds. -/
theorem reflected_prefix_lower_644 {z : ℝ} (hz : 0 ≤ z) :
    (∑ j ∈ Finset.range 6, (Nat.choose 5 j : ℝ) * z ^ (5 - j) * reflectedFloor644 j) ≤
      ∑ n ∈ Finset.Ioc 0 2701, ArithmeticFunction.vonMangoldt n * quarterReflectedWeight z n := by
  simp only [reflected_expand_644]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]
  exact
    Finset.sum_le_sum
      (fun j hj ↦
        mul_le_mul_of_nonneg_left
          (reflected_moment_lower_644 j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))
          (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hz _)))

end PseudoPrime.PrimeTestBounds.MillerRabin
