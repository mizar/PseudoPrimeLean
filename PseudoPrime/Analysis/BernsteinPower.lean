/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.BernsteinBounds
import Mathlib.Tactic

/-! # Conversion from power coefficients to Bernstein coefficients -/

public section

namespace PseudoPrime.Analysis

private theorem choose_weight (n j k : ℕ) (hj : j ≤ n) :
    (k.choose j : ℝ) / (n.choose j : ℝ) * (n.choose k : ℝ) =
      if j ≤ k then ((n - j).choose (k - j) : ℝ) else 0 := by
  by_cases hk : j ≤ k
  · rw [ite_eq_left hk, div_mul_eq_mul_div,
      div_eq_iff (Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.choose_pos hj)))]
    exact_mod_cast
      (mul_comm (k.choose j) (n.choose k)).trans
        ((Nat.choose_mul hk).trans (mul_comm (n.choose j) ((n - j).choose (k - j))))
  · rw [ite_eq_right hk, Nat.choose_eq_zero_of_lt (lt_of_not_ge hk), Nat.cast_zero, zero_div,
      zero_mul]

private theorem shifted_bernstein_term {n j : ℕ} (hj : j ≤ n) (k : ℕ) (t : ℝ) :
    ((j + k).choose j : ℝ) / (n.choose j : ℝ) *
        ((n.choose (j + k) : ℝ) * t ^ (j + k) * (1 - t) ^ (n - (j + k))) =
      t ^ j * (t ^ k * (1 - t) ^ (n - j - k) * ((n - j).choose k : ℝ)) := by
  rw [← mul_assoc, ← mul_assoc, choose_weight n j (j + k) hj, ite_eq_left (Nat.le_add_right _ _),
    Nat.add_sub_cancel_left, ← Nat.sub_sub, pow_add]
  ring

/-- A monomial of degree at most n is the Bernstein sum with coefficients
given by the corresponding binomial ratios. -/
theorem bernstein_power_term {n j : ℕ} (hj : j ≤ n) (t : Set.Icc (0 : ℝ) 1) :
    ∑ k : Fin (n + 1), ((k.val.choose j : ℝ) / (n.choose j : ℝ)) * bernstein n k t =
      (t : ℝ) ^ j := by
  simp only [bernstein_apply]
  let f (k : ℕ) :=
    ((k.choose j : ℝ) / (n.choose j : ℝ)) *
      ((n.choose k : ℝ) * (t : ℝ) ^ k * (1 - (t : ℝ)) ^ (n - k))
  change (∑ k : Fin (n + 1), f k.val) = _
  rw [Fin.sum_univ_eq_sum_range]
  dsimp only [f]
  have hn : n + 1 = j + (n - j + 1) := by rw [← Nat.add_assoc, Nat.add_sub_of_le hj]
  rw [hn, Finset.sum_range_add]
  have hzero :
    (∑ k ∈ Finset.range j,
        ((k.choose j : ℝ) / (n.choose j : ℝ)) *
          ((n.choose k : ℝ) * (t : ℝ) ^ k * (1 - (t : ℝ)) ^ (n - k))) =
      0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [Nat.choose_eq_zero_of_lt (Finset.mem_range.mp hk), Nat.cast_zero, zero_div, zero_mul]
  rw [hzero, zero_add]
  simp_rw [shifted_bernstein_term hj]
  rw [← Finset.mul_sum, ← add_pow, add_sub_cancel, one_pow, mul_one]

/-- The coefficients of a power polynomial of degree at most n convert to
Bernstein coefficients by a finite linear transform. -/
theorem bernstein_power_sum (n : ℕ) (a : Fin (n + 1) → ℝ) (t : Set.Icc (0 : ℝ) 1) :
    (∑ k : Fin (n + 1),
        (∑ j : Fin (n + 1), a j * ((k.val.choose j.val : ℝ) / (n.choose j.val : ℝ))) *
          bernstein n k t) =
      ∑ j : Fin (n + 1), a j * (t : ℝ) ^ j.val := by
  simp_rw [Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.mul_sum, bernstein_power_term (Nat.le_of_lt_succ j.isLt)]

end PseudoPrime.Analysis
