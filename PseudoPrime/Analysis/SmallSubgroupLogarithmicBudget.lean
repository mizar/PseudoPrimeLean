/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.PrimeProductLogarithmicBudget

/-! # Product-count budgets for small subgroups -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- If log(C)<=beta L and k log L>=cL with c(b-1)>beta, k<=L and M>=2L^b,
then C*k^k<(M+1-k)^k. Retain the lower bound M-k>=L^b and compare logarithms.
This generalizes the MR kernel count to arbitrary subgroup cardinal exponents. -/
theorem subgroup_power_budget_of_log_scale {p M k : ℕ} {L b c beta : ℝ} (hp : 0 < p) (hL : 1 < L)
    (hb : 1 < b) (hc : beta < c * (b - 1)) (hk : 0 < k) (hkL : (k : ℝ) ≤ L)
    (hceil : c * L ≤ (k : ℝ) * Real.log L) (hM : 2 * L ^ b ≤ (M : ℝ))
    (hplog : Real.log p ≤ beta * L) : p * k ^ k < (M + 1 - k) ^ k := by
  have hLp : 0 < L := zero_lt_one.trans hL
  have hpowpos := Real.rpow_pos_of_pos hLp b
  have hLpow : L ≤ L ^ b := by
    simpa only [Real.rpow_one] using (Real.rpow_le_rpow_of_exponent_le hL.le hb.le)
  have hkM : k ≤ M + 1 := by
    apply (Nat.cast_le (α := ℝ)).mp
    rw [Nat.cast_add, Nat.cast_one]
    linarith only [hkL, hLpow, hM, hpowpos]
  have hN : L ^ b ≤ ((M + 1 - k : ℕ) : ℝ) := by
    rw [Nat.cast_sub hkM, Nat.cast_add, Nat.cast_one]
    linarith only [hkL, hLpow, hM, hpowpos]
  have hNp : 0 < M + 1 - k := Nat.cast_pos.mp (hpowpos.trans_le hN)
  have hNk := Real.log_le_log hpowpos hN
  rw [Real.log_rpow hLp b] at hNk
  have hkl := Real.log_le_log (Nat.cast_pos.mpr hk) hkL
  have hdiff : (b - 1) * Real.log L ≤ Real.log (M + 1 - k : ℕ) - Real.log k := by
    linarith only [hNk, hkl]
  have hm := mul_le_mul_of_nonneg_left hdiff (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  have hmceil := mul_le_mul_of_nonneg_left hceil (sub_pos.mpr hb).le
  have hgt : beta * L < (k : ℝ) * (Real.log (M + 1 - k : ℕ) - Real.log k) := by
    calc
      beta * L < (c * (b - 1)) * L := mul_lt_mul_of_pos_right hc hLp
      _ ≤ (b - 1) * ((k : ℝ) * Real.log L) := by nlinarith only [hmceil]
      _ = (k : ℝ) * ((b - 1) * Real.log L) := by ring
      _ ≤ (k : ℝ) * (Real.log (M + 1 - k : ℕ) - Real.log k) := hm
  have hlog : Real.log p + (k : ℝ) * Real.log k < (k : ℝ) * Real.log (M + 1 - k : ℕ) := by
    nlinarith only [hgt, hplog]
  exact nat_mul_self_power_lt_of_log hp hNp hk hlog

/-- For 0<beta<1 and A>1/(1-beta), choose b,c with 1<b<A, cA<1 and
c(b-1)>beta. Select c between beta/(A-1) and 1/A, then b between 1+beta/c and A.
These strict margins handle product size and subgroup cardinality simultaneously. -/
theorem choose_subgroup_count_parameters {beta A : ℝ} (hbeta : 0 < beta) (hb1 : beta < 1)
    (hA : 1 / (1 - beta) < A) :
    ∃ b c : ℝ, 1 < b ∧ b < A ∧ 0 < c ∧ c * A < 1 ∧ beta < c * (b - 1) := by
  have hden : 0 < 1 - beta := sub_pos.mpr hb1
  have hquot : 1 < 1 / (1 - beta) := (one_lt_div hden).mpr (by linarith only [hbeta])
  have hA1 : 1 < A := hquot.trans hA
  have hAp : 0 < A := zero_lt_one.trans hA1
  have hAm : 0 < A - 1 := sub_pos.mpr hA1
  have hmain := (div_lt_iff₀ hden).mp hA
  have hint : beta / (A - 1) < 1 / A := by
    apply (div_lt_div_iff₀ hAm hAp).mpr
    nlinarith only [hmain]
  obtain ⟨c, hc1, hc2⟩ := exists_between hint
  have hc : 0 < c := (div_pos hbeta hAm).trans hc1
  have hcA : c * A < 1 := (lt_div_iff₀ hAp).mp hc2
  have hcb := (div_lt_iff₀ hAm).mp hc1
  have hbint : 1 + beta / c < A := by
    have hi : beta / c < A - 1 := (div_lt_iff₀ hc).mpr (by nlinarith only [hcb])
    linarith only [hi]
  obtain ⟨b, hb, hbA⟩ := exists_between hbint
  have hb1 : 1 < b := by linarith only [hb, div_pos hbeta hc]
  have hprod : beta < c * (b - 1) := by
    have hi : beta / c < b - 1 := by linarith only [hb]
    have hm := (div_lt_iff₀ hc).mp hi
    nlinarith only [hm]
  exact ⟨b, c, hb1, hbA, hc, hcA, hprod⟩

end PseudoPrime.Analysis
