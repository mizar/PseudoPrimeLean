/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.HeilbronnEnergyAlternatives
public import PseudoPrime.Analysis.LogarithmicMomentScales
public import PseudoPrime.Analysis.ThirteenthLogEnergyBudget

/-! # Explicit 32/13 Heilbronn energy bound -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- For every odd prime p, the actual Heilbronn additive energy satisfies
E¹³≤2¹⁹²p³²(1+ln p)¹⁴. Apply the proved truncated-band alternatives,
normalize the third moment and band count, and include the small diagonal
case by the elementary energy bound. No energy, correlation, tail or
asymptotic estimate is assumed. This is the closed energy input for the
improved non-squarefree Miller–Rabin witness exponent. -/
theorem heilbronnEnergy_thirteenth_le_log {p : ℕ} [Fact p.Prime] (hodd : Odd p) :
    (heilbronnEnergy p : ℝ) ^ 13 ≤ 2 ^ 192 * (p : ℝ) ^ 32 * (1 + Real.log p) ^ 14 := by
  have hp : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  have hL : (1 : ℝ) ≤ 1 + Real.log p := by linarith only [Real.log_natCast_nonneg p]
  have hEp : (heilbronnEnergy p : ℝ) ≤ (p : ℝ) ^ 3 := by
    exact_mod_cast heilbronnEnergy_le_cube.trans (Nat.pow_le_pow_left (Nat.sub_le p 1) 3)
  by_cases hd : 4 * (p - 1) ^ 2 ≤ heilbronnEnergy p
  · have ht := heilbronnThirdEnergy_le_log hodd
    have hC :=
      mul_le_mul_of_nonneg_right (by norm_num only : (786433 : ℝ) ≤ 2 ^ 20)
        (mul_nonneg (pow_nonneg (Nat.cast_nonneg p) 3) (zero_le_one.trans hL))
    have hTb : (heilbronnThirdEnergy p : ℝ) ≤ 2 ^ 20 * (p : ℝ) ^ 3 * (1 + Real.log p) := by
      nlinarith only [ht, hC]
    have hJ : (1 : ℝ) ≤ ((Nat.log2 p + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le (Nat.log2 p))
    exact
      PseudoPrime.Analysis.thirteenth_log_budget_of_alternatives (Nat.cast_nonneg _)
        (Nat.cast_nonneg _) (Nat.cast_nonneg _) hJ (zero_le_one.trans hL) hEp
        (PseudoPrime.Analysis.one_add_log_sq_le_four_mul hp) hTb
        (PseudoPrime.Analysis.log2_succ_le_two_mul_one_add_log p)
        (heilbronnEnergy_third_moment_alternatives hodd hd)
  · have hb : heilbronnEnergy p ≤ 4 * p ^ 2 :=
      (lt_of_not_ge hd).le.trans (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left (Nat.sub_le p 1) 2))
    exact
      PseudoPrime.Analysis.thirteenth_log_budget_of_small_energy (Nat.one_le_cast.mpr hp)
        (Nat.cast_nonneg _) hL (by exact_mod_cast hb)

end PseudoPrime.NumberTheory.Heilbronn
