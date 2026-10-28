/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TwoPoleSmallPrefixSavings
public import PseudoPrime.LLS.PairedEulerConductorBudget

/-! # Rational prime costs for the paired Euler conductor budget -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- For nonnegative a and b, a lower bound b^4 at most a^m implies b at most a^(m/4).
Raise both sides to the positive fourth power. This converts rational power comparisons into
small exact integer inequalities without numerical real-power evaluation. -/
theorem rpow_lower_of_fourth_power {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (m : ℕ) (h : b ^ 4 ≤ a ^ m) :
    b ≤ a ^ ((m : ℝ) / 4) := by
  apply (Real.rpow_le_rpow_iff hb (Real.rpow_nonneg ha _) (by norm_num only : (0 : ℝ) < 4)).mp
  rw [← Real.rpow_mul ha, div_mul_cancel₀ _ (by norm_num only : (4 : ℝ) ≠ 0), Real.rpow_natCast,
    Real.rpow_ofNat]
  exact h

/-- For every prime p, the paired Euler weight is at most (3/10) log p, with the additional
allowance (1/5) log 2 only at two. Bound the denominators by rational fourth-power comparisons
and use a tangent bound for log p when p is at least three. This scalar bound charges the
unramified prime prefix to the conductor quotient. -/
theorem pairedEulerPrefixWeight_prime_upper_three_tenths {p : ℕ} (hp : p.Prime) :
    pairedEulerPrefixWeight (5 / 4) (11 / 4) (3 / 4) p ≤
      (3 / 10 : ℝ) * Real.log p + if p = 2 then (1 / 5 : ℝ) * Real.log 2 else 0 := by
  have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr hp.pos
  have hl0 := Real.log_natCast_nonneg p
  have hw :
    pairedEulerPrefixWeight (5 / 4) (11 / 4) (3 / 4) p =
      Real.log p *
        (1 / (p : ℝ) ^ (5 / 4 : ℝ) + (3 / 4 : ℝ) * Real.log p / (p : ℝ) ^ (11 / 4 : ℝ)) := by
    dsimp only [pairedEulerPrefixWeight]
    rw [ArithmeticFunction.vonMangoldt_apply_prime hp]
    ring
  rw [hw]
  by_cases he : p = 2
  · subst p
    rw [ite_eq_left rfl]
    have h5 : (19 / 8 : ℝ) ≤ (2 : ℝ) ^ (5 / 4 : ℝ) :=
      rpow_lower_of_fourth_power (by norm_num only) (by norm_num only) 5 (by norm_num only)
    have h11 : (67 / 10 : ℝ) ≤ (2 : ℝ) ^ (11 / 4 : ℝ) :=
      rpow_lower_of_fourth_power (by norm_num only) (by norm_num only) 11 (by norm_num only)
    have hd5 := Real.rpow_pos_of_pos (show (0 : ℝ) < 2 by norm_num only) (5 / 4 : ℝ)
    have hd11 := Real.rpow_pos_of_pos (show (0 : ℝ) < 2 by norm_num only) (11 / 4 : ℝ)
    have hb5 : 1 / (2 : ℝ) ^ (5 / 4 : ℝ) ≤ 8 / 19 := (div_le_iff₀ hd5).mpr (by linarith only [h5])
    have hl : Real.log 2 ≤ 7 / 10 := by linarith only [Real.log_two_lt_d9]
    have hb11 : (3 / 4 : ℝ) * Real.log 2 / (2 : ℝ) ^ (11 / 4 : ℝ) ≤ 21 / 268 :=
      (div_le_iff₀ hd11).mpr (by linarith only [h11, hl])
    have hb :
      1 / (2 : ℝ) ^ (5 / 4 : ℝ) + (3 / 4 : ℝ) * Real.log 2 / (2 : ℝ) ^ (11 / 4 : ℝ) ≤ 1 / 2 := by
      linarith only [hb5, hb11]
    have hm := mul_le_mul_of_nonneg_left hb hl0
    linarith only [hm]
  · rw [ite_eq_right he, add_zero]
    have hp3 : 3 ≤ p := Nat.succ_le_of_lt (lt_of_le_of_ne hp.two_le (Ne.symm he))
    have hp3r : (3 : ℝ) ≤ p := Nat.cast_le.mpr hp3
    have ht := Real.log_le_sub_one_of_pos (div_pos hp0 (by norm_num only : (0 : ℝ) < 3))
    rw [Real.log_div hp0.ne' (by norm_num only : (3 : ℝ) ≠ 0)] at ht
    have hl3 : Real.log 3 ≤ 9 / 8 := by linarith only [Real.log_three_lt_d9]
    have hl : Real.log p ≤ (3 / 8 : ℝ) * p := by linarith only [ht, hl3, hp3r]
    have h5 : (39 / 10 : ℝ) ≤ (p : ℝ) ^ (5 / 4 : ℝ) :=
      (rpow_lower_of_fourth_power (by norm_num only : (0 : ℝ) ≤ 3) (by norm_num only) 5
            (by norm_num only)).trans
        (Real.rpow_le_rpow (by norm_num only) hp3r (by norm_num only))
    have h7 : (13 / 2 : ℝ) ≤ (p : ℝ) ^ (7 / 4 : ℝ) :=
      (rpow_lower_of_fourth_power (by norm_num only : (0 : ℝ) ≤ 3) (by norm_num only) 7
            (by norm_num only)).trans
        (Real.rpow_le_rpow (by norm_num only) hp3r (by norm_num only))
    have hd5 := Real.rpow_pos_of_pos hp0 (5 / 4 : ℝ)
    have hd11 := Real.rpow_pos_of_pos hp0 (11 / 4 : ℝ)
    have hb5 : 1 / (p : ℝ) ^ (5 / 4 : ℝ) ≤ 10 / 39 := (div_le_iff₀ hd5).mpr (by linarith only [h5])
    have hid : (p : ℝ) ^ (11 / 4 : ℝ) = p * (p : ℝ) ^ (7 / 4 : ℝ) := by
      rw [show (11 / 4 : ℝ) = 1 + 7 / 4 by norm_num only, Real.rpow_add hp0, Real.rpow_one]
    have hb11 : (3 / 4 : ℝ) * Real.log p / (p : ℝ) ^ (11 / 4 : ℝ) ≤ 9 / 208 := by
      apply (div_le_iff₀ hd11).mpr
      rw [hid]
      have hm := mul_le_mul_of_nonneg_left h7 hp0.le
      nlinarith only [hl, hm]
    have hb :
      1 / (p : ℝ) ^ (5 / 4 : ℝ) + (3 / 4 : ℝ) * Real.log p / (p : ℝ) ^ (11 / 4 : ℝ) ≤ 3 / 10 := by
      linarith only [hb5, hb11]
    exact (mul_le_mul_of_nonneg_left hb hl0).trans_eq (mul_comm _ _)

end PseudoPrime.AnalyticNumberTheory.Arithmetic
