/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ThirdMomentEnergyAlternatives

/-! # Absorbing cubic energy alternatives into a thirteenth-power log budget -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- A cubic bound E³≤Ap⁷L⁴ and E≤p³ imply E¹³≤4A⁴p³²L¹⁴ when L²≤4p.
Raise the cubic inequality to the fourth power, multiply by the elementary
energy bound, and absorb two logarithmic powers. All constants are explicit. -/
theorem thirteenth_le_of_cubic_log_budget {p E L A : ℝ} (hp : 0 ≤ p) (hE : 0 ≤ E) (hL : 0 ≤ L)
    (hA : 0 ≤ A) (hEp : E ≤ p ^ 3) (hc : E ^ 3 ≤ A * p ^ 7 * L ^ 4) (hL2 : L ^ 2 ≤ 4 * p) :
    E ^ 13 ≤ 4 * A ^ 4 * p ^ 32 * L ^ 14 := by
  have hs := pow_le_pow_left₀ (pow_nonneg hE 3) hc 4
  have hu :=
    mul_le_mul hs hEp hE
      (pow_nonneg (mul_nonneg (mul_nonneg hA (pow_nonneg hp 7)) (pow_nonneg hL 4)) 4)
  have hl :=
    mul_le_mul_of_nonneg_left hL2
      (mul_nonneg (mul_nonneg (pow_nonneg hA 4) (pow_nonneg hp 31)) (pow_nonneg hL 14))
  nlinarith only [hu, hl]

/-- With T≤2²⁰p³L and J≤2L, the main-term cubic bound is absorbed into
2¹⁹²p³²L¹⁴. First normalize its coefficient to E³≤2³⁴p⁷L⁴ and use the
generic cubic-to-thirteenth comparison. This controls the non-error alternative. -/
theorem thirteenth_log_budget_of_main_cubic {p E T J L : ℝ} (hp : 0 ≤ p) (hE : 0 ≤ E) (hJ : 0 ≤ J)
    (hL : 0 ≤ L) (hEp : E ≤ p ^ 3) (hL2 : L ^ 2 ≤ 4 * p) (hTb : T ≤ 2 ^ 20 * p ^ 3 * L)
    (hJb : J ≤ 2 * L) (hc : E ^ 3 ≤ 2048 * p ^ 4 * T * J ^ 3) :
    E ^ 13 ≤ 2 ^ 192 * p ^ 32 * L ^ 14 := by
  have hJ3 := pow_le_pow_left₀ hJ hJb 3
  have hTJ :=
    mul_le_mul hTb hJ3 (pow_nonneg hJ 3)
      (mul_nonneg (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2 ^ 20) (pow_nonneg hp 3)) hL)
  have hs :=
    mul_le_mul_of_nonneg_left hTJ (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2048) (pow_nonneg hp 4))
  have hn : E ^ 3 ≤ 2 ^ 34 * p ^ 7 * L ^ 4 := by nlinarith only [hc, hs]
  have h13 :=
    thirteenth_le_of_cubic_log_budget hp hE hL (by norm_num only : (0 : ℝ) ≤ 2 ^ 34) hEp hn hL2
  have hC : (4 : ℝ) * (2 ^ 34) ^ 4 ≤ 2 ^ 192 := by norm_num only
  have hM := mul_le_mul_of_nonneg_right hC (mul_nonneg (pow_nonneg hp 32) (pow_nonneg hL 14))
  nlinarith only [h13, hM]

end PseudoPrime.Analysis
