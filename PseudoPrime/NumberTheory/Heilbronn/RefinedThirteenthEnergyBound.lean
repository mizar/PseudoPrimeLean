/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.ThirteenthEnergyBound
public import PseudoPrime.Analysis.ParameterizedThirteenthLogBudget

/-! # A smaller explicit coefficient for the 32/13 Heilbronn energy bound -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- Every odd prime p satisfies E^13<=2^176 p^32(1+ln p)^14.
Keep the proved third-moment coefficient 786433 and the sharper dyadic
coefficient 3/2 in the actual energy alternatives. This improves the old
coefficient by 2^16 without changing its p or logarithmic exponents. -/
theorem heilbronnEnergy_thirteenth_le_log_refined {p : ℕ} [Fact p.Prime] (hodd : Odd p) :
    (heilbronnEnergy p : ℝ) ^ 13 ≤ 2 ^ 176 * (p : ℝ) ^ 32 * (1 + Real.log p) ^ 14 := by
  have hp : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  have hL : (1 : ℝ) ≤ 1 + Real.log p := by linarith only [Real.log_natCast_nonneg p]
  have hEp : (heilbronnEnergy p : ℝ) ≤ (p : ℝ) ^ 3 := by
    exact_mod_cast heilbronnEnergy_le_cube.trans (Nat.pow_le_pow_left (Nat.sub_le p 1) 3)
  by_cases hd : 4 * (p - 1) ^ 2 ≤ heilbronnEnergy p
  · have hJ : (1 : ℝ) ≤ ((Nat.log2 p + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le (Nat.log2 p))
    exact
      PseudoPrime.Analysis.refined_thirteenth_budget_of_alternatives (Nat.cast_nonneg _)
        (Nat.cast_nonneg _) (Nat.cast_nonneg _) hJ (zero_le_one.trans hL) hEp
        (PseudoPrime.Analysis.one_add_log_sq_le_four_mul hp) (heilbronnThirdEnergy_le_log hodd)
        (PseudoPrime.Analysis.log2_succ_le_three_halves_one_add_log p)
        (heilbronnEnergy_third_moment_alternatives hodd hd)
  · have hb : heilbronnEnergy p ≤ 4 * p ^ 2 :=
      (lt_of_not_ge hd).le.trans (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left (Nat.sub_le p 1) 2))
    exact
      PseudoPrime.Analysis.refined_thirteenth_budget_of_small_energy (Nat.one_le_cast.mpr hp)
        (Nat.cast_nonneg _) hL (by exact_mod_cast hb)

/-- The refined energy coefficient gives the exact counting power budget
whenever its displayed logarithmic slack holds. Raise the closed energy
bound to a, multiply by D^(13a), and cancel the positive prime power.
This exposes the smaller coefficient to finite-scale counting consumers. -/
theorem thirteenth_energy_power_lt_of_refined_log_slack {p : ℕ} [Fact p.Prime] (hodd : Odd p)
    (a D r : ℕ)
    (hlarge : (2 ^ 176 : ℝ) ^ a * (D : ℝ) ^ (13 * a) * (1 + Real.log p) ^ (14 * a) < (p : ℝ) ^ r) :
    (heilbronnEnergy p * D) ^ (13 * a) < p ^ (32 * a + r) := by
  have he :=
    pow_le_pow_left₀ (pow_nonneg (Nat.cast_nonneg (heilbronnEnergy p)) 13)
      (heilbronnEnergy_thirteenth_le_log_refined hodd) a
  have hb :
    ((heilbronnEnergy p : ℝ) * D) ^ (13 * a) ≤
      ((2 ^ 176 : ℝ) ^ a * (D : ℝ) ^ (13 * a) * (1 + Real.log p) ^ (14 * a)) *
        (p : ℝ) ^ (32 * a) := by
    convert mul_le_mul_of_nonneg_right he (pow_nonneg (Nat.cast_nonneg D) (13 * a)) using 1 <;>
      simp only [mul_pow, ← pow_mul]
    ring
  have hs :=
    mul_lt_mul_of_pos_right hlarge
      (pow_pos (Nat.cast_pos.mpr (Fact.out : p.Prime).pos : (0 : ℝ) < p) (32 * a))
  have hid : (p : ℝ) ^ r * (p : ℝ) ^ (32 * a) = (p : ℝ) ^ (32 * a + r) := by
    rw [← pow_add, Nat.add_comm]
  exact_mod_cast hb.trans_lt (hs.trans_eq hid)

end PseudoPrime.NumberTheory.Heilbronn
