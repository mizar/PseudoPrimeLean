/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ExplicitLogSqrtAbsorption
public import PseudoPrime.Analysis.QuadraticGammaNumerics

/-! # Explicit original-level error budgets for quadratic Gamma comparisons -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For L≥16, K≤2 and scale x=(32/99)L², the index-two finite modulus
loss at cutoff (99/40)x is at most 18log(L).
Use sqrt(x)≥L/2, log(2)≥1/2, L+K≤9L/8, and the cutoff logarithm bound.
This retains the original-level Euler loss instead of discarding it in the quadratic comparison. -/
theorem gamma_quadratic_modulus_error_le_log {L K : ℝ} (hL : 16 ≤ L) (hK2 : K ≤ 2) :
    let x := (32 / 99 : ℝ) * L ^ 2
    2 * ((L + K) * Real.log ((99 / 40 : ℝ) * x) / (Real.log 2 * Real.sqrt x)) ≤
      18 * Real.log L := by
  intro x
  have hpos : 0 < L := lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 16) hL
  have hx0 : 0 ≤ x := mul_nonneg (by norm_num only) (sq_nonneg L)
  have hs : L / 2 ≤ Real.sqrt x :=
    Real.le_sqrt_of_sq_le
      (by
        dsimp only [x]
        nlinarith only [sq_nonneg L])
  have hs0 : 0 < Real.sqrt x := lt_of_lt_of_le (div_pos hpos (by norm_num only : (0 : ℝ) < 2)) hs
  have hx1 : 1 ≤ (99 / 40 : ℝ) * x := by
    dsimp only [x]
    nlinarith only [hL]
  have hlog : 0 ≤ Real.log L := Real.log_nonneg (le_trans (by norm_num only) hL)
  have hcutlog : 0 ≤ Real.log ((99 / 40 : ℝ) * x) := Real.log_nonneg hx1
  have hcl : Real.log ((99 / 40 : ℝ) * x) ≤ 2 * Real.log L := by
    have hh : (99 / 40 : ℝ) * x ≤ L ^ 2 := by
      dsimp only [x]
      nlinarith only [sq_nonneg L]
    have hl := Real.log_le_log (lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 1) hx1) hh
    rw [Real.log_pow] at hl
    norm_num only [Nat.cast_ofNat] at hl
    exact hl
  have hq : L + K ≤ (9 / 8 : ℝ) * L := by linarith only [hL, hK2]
  have hnum := mul_le_mul hq hcl hcutlog (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 9 / 8) hpos.le)
  have htwo : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith only [Real.log_two_gt_d9]
  have hd :=
    mul_le_mul htwo hs (div_nonneg hpos.le (by norm_num only : (0 : ℝ) ≤ 2))
      (htwo.trans' (by norm_num only : (0 : ℝ) ≤ 1 / 2))
  have hm := mul_le_mul_of_nonneg_left hd (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 9) hlog)
  have hi :
    (L + K) * Real.log ((99 / 40 : ℝ) * x) / (Real.log 2 * Real.sqrt x) ≤ 9 * Real.log L := by
    apply (div_le_iff₀ (mul_pos (lt_of_lt_of_le (by norm_num only) htwo) hs0)).mpr
    nlinarith only [hnum, hm]
  linarith only [hi]

/-- For L≥3·10¹⁰ and K≤2, the direct quadratic scale and cutoff exceed one,
and all original-level Gamma errors, including the finite modulus loss and mass shift,
are at most half of (7/5000)L. Bound them by 24040+18log(L)+39sqrt(L)
and apply the explicit absorption theorem.
This provides a concrete input-logarithm threshold for coefficient 4/5. -/
theorem gamma_quadratic_direct_error_budget {L K : ℝ} (hL : 30000000000 ≤ L) (hK2 : K ≤ 2) :
    let x := (32 / 99 : ℝ) * L ^ 2
    1 ≤ x ∧
      1 ≤ (99 / 40 : ℝ) * x ∧
      (11783423 / 25000000 : ℝ) * K + 39 * x ^ (1 / 4 : ℝ) + 39 +
          (10002 * (L + K) + 10004) / Real.sqrt x +
          2 * ((L + K) * Real.log ((99 / 40 : ℝ) * x) / (Real.log 2 * Real.sqrt x)) ≤
        (7 / 5000 : ℝ) * L / 2 := by
  intro x
  have h16 : (16 : ℝ) ≤ L := (by norm_num only : (16 : ℝ) ≤ 30000000000).trans hL
  have hpos : 0 < L := lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 16) h16
  have hx0 : 0 ≤ x := mul_nonneg (by norm_num only) (sq_nonneg L)
  have hx1 : 1 ≤ x := by
    dsimp only [x]; nlinarith only [h16]
  have hcut1 : 1 ≤ (99 / 40 : ℝ) * x := by
    dsimp only [x]; nlinarith only [h16]
  have hs : L / 2 ≤ Real.sqrt x :=
    Real.le_sqrt_of_sq_le
      (by
        dsimp only [x]
        nlinarith only [sq_nonneg L])
  have hs0 : 0 < Real.sqrt x := lt_of_lt_of_le (div_pos hpos (by norm_num only : (0 : ℝ) < 2)) hs
  have hsUpper : Real.sqrt x ≤ L := by
    have hu : x ≤ L ^ 2 := by
      dsimp only [x]; nlinarith only [sq_nonneg L]
    nlinarith only [hu, Real.sq_sqrt hx0, Real.sqrt_nonneg x, hpos]
  have hfourth : x ^ (1 / 4 : ℝ) ≤ Real.sqrt L := by
    have he : x ^ (1 / 4 : ℝ) = Real.sqrt (Real.sqrt x) := by
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hx0]
      congr 1
      norm_num only
    rw [he]
    exact Real.sqrt_le_sqrt hsUpper
  have hratio : (10002 * (L + K) + 10004) / Real.sqrt x ≤ 24000 := by
    apply (div_le_iff₀ hs0).mpr
    nlinarith only [hs, h16, hK2]
  have hconstant : (11783423 / 25000000 : ℝ) * K ≤ 1 := by nlinarith only [hK2]
  have hmod := gamma_quadratic_modulus_error_le_log h16 hK2
  have hf := mul_le_mul_of_nonneg_left hfourth (by norm_num only : (0 : ℝ) ≤ 39)
  have herr :=
    log_sqrt_error_le_half (A := (24040 : ℝ)) (B := (18 : ℝ)) (C := (39 : ℝ)) (δ := (7 / 5000 : ℝ))
      (by norm_num only) (by norm_num only) hpos
      ((by norm_num only : 4 * (24040 : ℝ) / (7 / 5000 : ℝ) ≤ 30000000000).trans hL)
      ((by norm_num only : (4 * ((18 : ℝ) + 39) / (7 / 5000 : ℝ)) ^ 2 ≤ 30000000000).trans hL)
  refine ⟨hx1, hcut1, ?_⟩
  dsimp only [x] at hratio hf ⊢
  nlinarith only [hconstant, hf, hratio, hmod, herr]

/-- For L≥3·10¹⁰ and K≤2, the index-two Gamma comparison at scale
(32/99)L² and cutoff multiplier 99/40 is impossible with the displayed original-level errors.
Absorb the complete remainder and combine the exponential and rational coefficient margins.
This is the numerical contradiction yielding the direct quadratic coefficient 4/5. -/
theorem gamma_quadratic_direct_inequality_false {L K : ℝ} (hL : 30000000000 ≤ L) (hK2 : K ≤ 2) :
    let x := (32 / 99 : ℝ) * L ^ 2
    ¬((1 - 2 * Real.exp (-(99 / 40 : ℝ))) * Real.sqrt x ≤
        (11783423 / 25000000 : ℝ) * (L + K) + 39 * x ^ (1 / 4 : ℝ) + 39 +
          (10002 * (L + K) + 10004) / Real.sqrt x +
          2 * ((L + K) * Real.log ((99 / 40 : ℝ) * x) / (Real.log 2 * Real.sqrt x))) := by
  intro x hcmp
  have hpos : 0 < L := lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 30000000000) hL
  obtain ⟨_, _, he⟩ := gamma_quadratic_direct_error_budget hL hK2
  have hstrict := gamma_quadratic_direct_main_term_lt hpos he
  have hd : (79 / 95 : ℝ) ≤ 1 - 2 * Real.exp (-(99 / 40 : ℝ)) := by
    linarith only [gamma_quadratic_exp_bound]
  have hm := mul_le_mul_of_nonneg_right hd (Real.sqrt_nonneg x)
  dsimp only [x] at hcmp hm
  nlinarith only [hstrict, hcmp, hm]

end PseudoPrime.Analysis
