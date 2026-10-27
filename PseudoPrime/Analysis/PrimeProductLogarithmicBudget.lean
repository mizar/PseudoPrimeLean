/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecificLimits.Basic

/-! # Logarithmic scales for prime-product counting -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- A strict inequality between logarithms yields p*k^k<N^k for positive p,N,k.
Expand the logarithms of products and powers and use strict monotonicity.
Used to turn the real counting gap into the natural power budget. -/
theorem nat_mul_self_power_lt_of_log {p N k : ℕ} (hp : 0 < p) (hN : 0 < N) (hk : 0 < k)
    (hlog : Real.log p + (k : ℝ) * Real.log k < (k : ℝ) * Real.log N) : p * k ^ k < N ^ k := by
  apply (Nat.cast_lt (α := ℝ)).mp
  rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_pow]
  have hpR : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  apply (Real.log_lt_log_iff (mul_pos hpR (pow_pos hkR k)) (pow_pos hNR k)).mp
  rw [Real.log_mul hpR.ne' (pow_ne_zero k hkR.ne'), Real.log_pow, Real.log_pow]
  exact hlog

/-- If log p<=L, k<=L, k*log L>=cL and pi-like count M>=2L^b,
with L>1, b>1 and c(b-1)>1, then (p-1)*k^k<(M+1-k)^k.
Retain M-k>=L^b and compare logarithms. This closes the subgroup count budget. -/
theorem prime_product_power_budget_of_log_scale {p M k : ℕ} {L b c : ℝ} (hp : 0 < p) (hL : 1 < L)
    (hb : 1 < b) (hc : 1 < c * (b - 1)) (hk : 0 < k) (hkL : (k : ℝ) ≤ L)
    (hceil : c * L ≤ (k : ℝ) * Real.log L) (hM : 2 * L ^ b ≤ (M : ℝ)) (hplog : Real.log p ≤ L) :
    (p - 1) * k ^ k < (M + 1 - k) ^ k := by
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
  have hgt : L < (k : ℝ) * (Real.log (M + 1 - k : ℕ) - Real.log k) := by
    calc
      L < (c * (b - 1)) * L := (lt_mul_iff_one_lt_left hLp).mpr hc
      _ ≤ (b - 1) * ((k : ℝ) * Real.log L) := by nlinarith only [hmceil]
      _ = (k : ℝ) * ((b - 1) * Real.log L) := by ring
      _ ≤ (k : ℝ) * (Real.log (M + 1 - k : ℕ) - Real.log k) := hm
  have hlog : Real.log p + (k : ℝ) * Real.log k < (k : ℝ) * Real.log (M + 1 - k : ℕ) := by
    nlinarith only [hgt, hplog]
  exact
    (Nat.mul_le_mul_right (k ^ k) (Nat.sub_le p 1)).trans_lt
      (nat_mul_self_power_lt_of_log hp hNp hk hlog)

/-- For c>0, L>=2 and log L>=2c, k=ceil(cL/log L) is positive and at most L.
It satisfies cL<=k log L and k<=cL/log L+1. Ceiling bounds preserve both sides
needed to compare the product size and the number of products. -/
theorem ceil_log_scale_bounds {L c : ℝ} (hc : 0 < c) (hL : 2 ≤ L) (hlogc : 2 * c ≤ Real.log L) :
    let k := Nat.ceil (c * L / Real.log L)
    0 < k ∧ (k : ℝ) ≤ L ∧ c * L ≤ (k : ℝ) * Real.log L ∧ (k : ℝ) ≤ c * L / Real.log L + 1 := by
  dsimp only
  have hLp : 0 < L := lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 2) hL
  have hlp : 0 < Real.log L := (mul_pos (by norm_num only) hc).trans_le hlogc
  have harg : 0 < c * L / Real.log L := div_pos (mul_pos hc hLp) hlp
  have hlo := Nat.le_ceil (c * L / Real.log L)
  have hhi := Nat.ceil_lt_add_one harg.le
  have hm := mul_le_mul_of_nonneg_right hlogc hLp.le
  have hhalf : c * L / Real.log L ≤ L / 2 := by
    apply (div_le_iff₀ hlp).mpr
    nlinarith only [hm]
  have hk : 0 < Nat.ceil (c * L / Real.log L) := Nat.cast_pos.mp (harg.trans_le hlo)
  refine ⟨hk, ?_, (div_le_iff₀ hlp).mp hlo, hhi.le⟩
  nlinarith only [hhi, hhalf, hL]

/-- If B<=L^A, log p=L and k<=cL/log L+1, the strict scale gap
cAL+A log L<aL implies B^k<p^a. Compare logarithms and keep the ceiling error.
This is the product-size half of the unconditional witness criterion. -/
theorem prime_power_product_lt_of_log_scale {p a B k : ℕ} {L A c : ℝ} (hp : 0 < p) (hB : 0 < B)
    (hL : 1 < L) (hA : 0 < A) (hBL : (B : ℝ) ≤ L ^ A) (hpk : Real.log p = L)
    (hk : (k : ℝ) ≤ c * L / Real.log L + 1) (hgap : c * A * L + A * Real.log L < (a : ℝ) * L) :
    B ^ k < p ^ a := by
  have hLp : 0 < L := zero_lt_one.trans hL
  have hlp := Real.log_pos hL
  have hlogB := Real.log_le_log (Nat.cast_pos.mpr hB) hBL
  rw [Real.log_rpow hLp A] at hlogB
  have hm1 := mul_le_mul_of_nonneg_left hlogB (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  have hm2 := mul_le_mul_of_nonneg_right hk (mul_pos hA hlp).le
  have hid : (c * L / Real.log L + 1) * (A * Real.log L) = c * A * L + A * Real.log L := by
    field_simp [hlp.ne']
  rw [hid] at hm2
  have hlt : (k : ℝ) * Real.log B < (a : ℝ) * Real.log p := by
    rw [hpk]
    exact hm1.trans_lt (hm2.trans_lt hgap)
  apply (Nat.cast_lt (α := ℝ)).mp
  rw [Nat.cast_pow, Nat.cast_pow]
  apply (Real.log_lt_log_iff (pow_pos (Nat.cast_pos.mpr hB) k) (pow_pos (Nat.cast_pos.mpr hp) a)).mp
  rw [Real.log_pow, Real.log_pow]
  exact hlt

/-- For a>1 and A>a/(a-1), choose 1<b<A and c>0 with cA<a and c(b-1)>1.
Select c between 1/(A-1) and a/A, then b between 1+1/c and A.
These strict margins simultaneously close product size and count comparisons. -/
theorem choose_log_count_parameters {a A : ℝ} (ha : 1 < a) (hA : a / (a - 1) < A) :
    ∃ b c : ℝ, 1 < b ∧ b < A ∧ 0 < c ∧ c * A < a ∧ 1 < c * (b - 1) := by
  have ham : 0 < a - 1 := sub_pos.mpr ha
  have hquot : 1 < a / (a - 1) := (one_lt_div ham).mpr (by linarith only)
  have hA1 : 1 < A := hquot.trans hA
  have hAm : 0 < A - 1 := sub_pos.mpr hA1
  have hAp : 0 < A := zero_lt_one.trans hA1
  have hmain := (div_lt_iff₀ ham).mp hA
  have hint : 1 / (A - 1) < a / A := by
    apply (div_lt_div_iff₀ hAm hAp).mpr
    nlinarith only [hmain]
  obtain ⟨c, hc1, hc2⟩ := exists_between hint
  have hc : 0 < c := (div_pos zero_lt_one hAm).trans hc1
  have hcA : c * A < a := (lt_div_iff₀ hAp).mp hc2
  have hcb := (div_lt_iff₀ hAm).mp hc1
  have hbint : 1 + 1 / c < A := by
    have hi : 1 / c < A - 1 := (div_lt_iff₀ hc).mpr (by nlinarith only [hcb])
    linarith only [hi]
  obtain ⟨b, hb1, hb2⟩ := exists_between hbint
  have hb : 1 < b := by linarith only [hb1, div_pos zero_lt_one hc]
  have hprod : 1 < c * (b - 1) := by
    have hi : 1 / c < b - 1 := by linarith only [hb1]
    have hm := (div_lt_iff₀ hc).mp hi
    nlinarith only [hm]
  exact ⟨b, c, hb, hb2, hc, hcA, hprod⟩

end PseudoPrime.Analysis
