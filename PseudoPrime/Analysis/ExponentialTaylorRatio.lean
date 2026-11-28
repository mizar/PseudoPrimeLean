/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic

/-! # Taylor remainder of the positive exponential with a geometric ratio -/

public section

namespace PseudoPrime.Analysis

private theorem exp_taylor_term_ratio {x q : ℝ} (hx : 0 ≤ x) {n : ℕ} (hr : x / (n + 1 : ℕ) ≤ q)
    (k : ℕ) : x ^ (n + k) / ((n + k).factorial : ℝ) ≤ x ^ n / (n.factorial : ℝ) * q ^ k := by
  have hp : (0 : ℝ) < (n + 1 : ℕ) := Nat.cast_pos.mpr (Nat.succ_pos n)
  have hf : (0 : ℝ) < n.factorial := Nat.cast_pos.mpr (Nat.factorial_pos n)
  have hd : (n.factorial : ℝ) * ((n + 1 : ℕ) : ℝ) ^ k ≤ ((n + k).factorial : ℝ) := by
    exact_mod_cast (Nat.factorial_mul_pow_le_factorial (n := k) (m := n))
  calc
    _ ≤ x ^ (n + k) / ((n.factorial : ℝ) * ((n + 1 : ℕ) : ℝ) ^ k) :=
      div_le_div_of_nonneg_left (pow_nonneg hx _) (mul_pos hf (pow_pos hp _)) hd
    _ = x ^ n / (n.factorial : ℝ) * (x / (n + 1 : ℕ)) ^ k := by
      rw [pow_add, div_pow, div_mul_div_comm]
    _ ≤ _ :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (div_nonneg hx hp.le) hr k)
        (div_nonneg (pow_nonneg hx _) hf.le)

/-- For a nonnegative input with Taylor ratio at most q, truncate the series
before degree n and bound the remaining terms by a geometric series. -/
theorem exp_le_taylor_ratio {x q : ℝ} {n : ℕ} (hx : 0 ≤ x) (hq₀ : 0 ≤ q) (hq₁ : q < 1)
    (hr : x / (n + 1 : ℕ) ≤ q) :
    Real.exp x ≤
      (∑ k ∈ Finset.range n, x ^ k / (k.factorial : ℝ)) + x ^ n / (n.factorial : ℝ) / (1 - q) := by
  have hs := NormedSpace.expSeries_div_hasSum_exp x
  have he := hs.summable.sum_add_tsum_nat_add n
  rw [hs.tsum_eq, ← Real.exp_eq_exp_ℝ] at he
  have ha : Summable (fun k : ℕ ↦ x ^ (n + k) / ((n + k).factorial : ℝ)) := by
    simpa only [Nat.add_comm n] using (summable_nat_add_iff n).mpr hs.summable
  have hq : ‖q‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_nonneg hq₀] using hq₁
  have hb :=
    ha.tsum_le_tsum (exp_taylor_term_ratio hx hr)
      ((summable_geometric_of_norm_lt_one hq).mul_left (x ^ n / (n.factorial : ℝ)))
  rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hq, ← div_eq_mul_inv] at hb
  rw [← he]
  exact add_le_add (le_refl _) (by simpa only [Nat.add_comm n] using hb)

end PseudoPrime.Analysis
