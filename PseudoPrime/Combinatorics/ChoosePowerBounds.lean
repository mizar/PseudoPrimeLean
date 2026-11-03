/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Data.Nat.Choose.Bounds

/-! # Power bounds for binomial coefficients -/

@[expose] public section

namespace PseudoPrime.Combinatorics

/-- The elementary power lower bound for a binomial coefficient, with no division.
Bound the descending factorial below and k! above by k^k. Used to turn analytic
prime-count estimates into a subgroup-size contradiction. -/
theorem choose_power_lower (M k : ℕ) : (M + 1 - k) ^ k ≤ k ^ k * Nat.choose M k := by
  calc
    (M + 1 - k) ^ k ≤ M.descFactorial k := Nat.pow_sub_le_descFactorial M k
    _ = k.factorial * Nat.choose M k := Nat.descFactorial_eq_factorial_mul_choose M k
    _ ≤ k ^ k * Nat.choose M k := Nat.mul_le_mul_right (Nat.choose M k) (Nat.factorial_le_pow k)

/-- A strict power budget C*k^k < (M+1-k)^k implies C < choose(M,k).
Contradict the preceding lower bound. This avoids evaluating a large binomial
coefficient when applying the prime-product witness criterion. -/
theorem card_lt_choose_of_power_budget {C M k : ℕ} (h : C * k ^ k < (M + 1 - k) ^ k) :
    C < Nat.choose M k := by
  by_contra hn
  have hc : Nat.choose M k ≤ C := Nat.le_of_not_gt hn
  have hb := (choose_power_lower M k).trans (Nat.mul_le_mul_left (k ^ k) hc)
  rw [Nat.mul_comm C] at h
  exact Nat.not_lt_of_ge hb h

end PseudoPrime.Combinatorics
