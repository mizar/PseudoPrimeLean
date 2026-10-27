/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.CubicLogEnergyBudget

/-! # A common explicit thirteenth-power budget for all energy alternatives -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Normalize the error alternative using T≤2²⁰p³L and J≤2L. Multiply
their sixth and eighth powers and absorb the exact numerical coefficient
into 2¹⁹². This gives the target p³²L¹⁴ without an asymptotic exception. -/
theorem thirteenth_log_budget_of_error {p E T J L : ℝ} (hp : 0 ≤ p) (hT : 0 ≤ T) (hJ : 0 ≤ J)
    (hL : 0 ≤ L) (hTb : T ≤ 2 ^ 20 * p ^ 3 * L) (hJb : J ≤ 2 * L)
    (he : E ^ 13 ≤ 10995116277760000 * p ^ 14 * T ^ 6 * J ^ 8) :
    E ^ 13 ≤ 2 ^ 192 * p ^ 32 * L ^ 14 := by
  have hT6 := pow_le_pow_left₀ hT hTb 6
  have hJ8 := pow_le_pow_left₀ hJ hJb 8
  have hTJ :=
    mul_le_mul hT6 hJ8 (pow_nonneg hJ 8)
      (pow_nonneg
        (mul_nonneg (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2 ^ 20) (pow_nonneg hp 3)) hL) 6)
  have hs :=
    mul_le_mul_of_nonneg_left hTJ
      (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 10995116277760000) (pow_nonneg hp 14))
  have hC : (10995116277760000 : ℝ) * (2 ^ 20) ^ 6 * 2 ^ 8 ≤ 2 ^ 192 := by norm_num only
  have hM := mul_le_mul_of_nonneg_right hC (mul_nonneg (pow_nonneg hp 32) (pow_nonneg hL 14))
  nlinarith only [he, hs, hM]

/-- All three proved energy alternatives imply the common p³²L¹⁴ budget.
For J≥1, enlarge the diagonal cubic case to the main cubic case; apply
the cubic or error normalization. This combines the contributions while
keeping the original third-moment comparison fully explicit. -/
theorem thirteenth_log_budget_of_alternatives {p E T J L : ℝ} (hp : 0 ≤ p) (hE : 0 ≤ E) (hT : 0 ≤ T)
    (hJ : 1 ≤ J) (hL : 0 ≤ L) (hEp : E ≤ p ^ 3) (hL2 : L ^ 2 ≤ 4 * p) (hTb : T ≤ 2 ^ 20 * p ^ 3 * L)
    (hJb : J ≤ 2 * L)
    (ha :
      E ^ 3 ≤ 40 * p ^ 4 * T * J ∨
        E ^ 3 ≤ 2048 * p ^ 4 * T * J ^ 3 ∨ E ^ 13 ≤ 10995116277760000 * p ^ 14 * T ^ 6 * J ^ 8) :
    E ^ 13 ≤ 2 ^ 192 * p ^ 32 * L ^ 14 := by
  have hJ0 : 0 ≤ J := zero_le_one.trans hJ
  rcases ha with hd | hm | he
  · have hJ13 : J ≤ J ^ 3 := by simpa only [pow_one] using pow_le_pow_right₀ hJ (by decide : 1 ≤ 3)
    have h₁ :=
      mul_le_mul_of_nonneg_left hJ13
        (mul_nonneg (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 40) (pow_nonneg hp 4)) hT)
    have h₂ :=
      mul_le_mul_of_nonneg_right (by norm_num only : (40 : ℝ) ≤ 2048)
        (mul_nonneg (mul_nonneg (pow_nonneg hp 4) hT) (pow_nonneg hJ0 3))
    have hc : E ^ 3 ≤ 2048 * p ^ 4 * T * J ^ 3 := by nlinarith only [hd, h₁, h₂]
    exact thirteenth_log_budget_of_main_cubic hp hE hJ0 hL hEp hL2 hTb hJb hc
  · exact thirteenth_log_budget_of_main_cubic hp hE hJ0 hL hEp hL2 hTb hJb hm
  · exact thirteenth_log_budget_of_error hp hT hJ0 hL hTb hJb he

/-- The elementary small-energy case E≤4p² also fits 2¹⁹²p³²L¹⁴ for
p,L≥1. Raise its inequality to the thirteenth power and enlarge the
coefficient and p-exponent. This closes the exceptional diagonal range. -/
theorem thirteenth_log_budget_of_small_energy {p E L : ℝ} (hp : 1 ≤ p) (hE : 0 ≤ E) (hL : 1 ≤ L)
    (hb : E ≤ 4 * p ^ 2) : E ^ 13 ≤ 2 ^ 192 * p ^ 32 * L ^ 14 := by
  have hp0 : 0 ≤ p := zero_le_one.trans hp
  have hs := pow_le_pow_left₀ hE hb 13
  have hp26 := pow_le_pow_right₀ hp (by decide : 26 ≤ 32)
  have hC : (4 : ℝ) ^ 13 ≤ 2 ^ 192 := by norm_num only
  have hm := mul_le_mul hC hp26 (pow_nonneg hp0 26) (by norm_num only : (0 : ℝ) ≤ 2 ^ 192)
  have hb' : E ^ 13 ≤ 2 ^ 192 * p ^ 32 := by nlinarith only [hs, hm]
  have hL14 : 1 ≤ L ^ 14 := one_le_pow₀ hL
  have ht :=
    mul_le_mul_of_nonneg_left hL14
      (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2 ^ 192) (pow_nonneg hp0 32))
  nlinarith only [hb', ht]

end PseudoPrime.Analysis
