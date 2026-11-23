/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaCriticalLine
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-! # Explicit critical-line Gamma tail bound -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The endpoint exponential error 771 exp(-24) is below 1/40000.
A rational lower bound 5/2 for exp(1), raised to the twenty-fourth power, proves the gate. -/
private theorem gammaResolvent_exp_tail_gate : (771 : ℝ) * Real.exp (-24) < 1 / 40000 := by
  have he : (5 / 2 : ℝ) < Real.exp 1 := by linarith only [Real.exp_one_gt_d9]
  have hp : (5 / 2 : ℝ) ^ 24 < Real.exp 24 := by
    rw [show (24 : ℝ) = (24 : ℕ) * 1 by norm_num only, Real.exp_natCast_mul]
    exact pow_lt_pow_left₀ he (by norm_num only) (by norm_num only)
  have hn : (771 * 40000 : ℝ) < (5 / 2 : ℝ) ^ 24 := by norm_num only
  rw [Real.exp_neg, ← div_eq_mul_inv]
  exact (div_lt_iff₀ (Real.exp_pos 24)).mpr (by linarith only [hn, hp])

/-- For t≥16, (1+t²)exp(-3t/2) is at most 257 exp(-24).
The elementary exponential inequality controls t/16 and its square; exponential
multiplication then absorbs growth in the polynomial without a derivative estimate. -/
private theorem gammaResolvent_scaled_exp_tail {t : ℝ} (ht : 16 ≤ t) :
    (1 + t ^ 2) * Real.exp (-(3 / 2) * t) ≤ 257 * Real.exp (-24) := by
  have ht0 : 0 ≤ t := (by norm_num only : (0 : ℝ) ≤ 16).trans ht
  have hlin : t / 16 ≤ Real.exp ((t - 16) / 16) := by
    have h := Real.add_one_le_exp ((t - 16) / 16)
    linarith only [h]
  have hs := pow_le_pow_left₀ (div_nonneg ht0 (by norm_num only)) hlin 2
  have hex : Real.exp ((t - 16) / 16) ^ 2 = Real.exp ((t - 16) / 8) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hex] at hs
  have hone : 1 ≤ Real.exp ((t - 16) / 8) :=
    Real.one_le_exp_iff.mpr (div_nonneg (sub_nonneg.mpr ht) (by norm_num only))
  have hpoly : 1 + t ^ 2 ≤ 257 * Real.exp ((t - 16) / 8) := by nlinarith only [hs, hone]
  have hm := mul_le_mul_of_nonneg_right hpoly (Real.exp_pos (-(3 / 2) * t)).le
  have hprod : Real.exp ((t - 16) / 8) * Real.exp (-(3 / 2) * t) ≤ Real.exp (-24) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith only [ht])
  calc
    _ ≤ 257 * Real.exp ((t - 16) / 8) * Real.exp (-(3 / 2) * t) := hm
    _ = 257 * (Real.exp ((t - 16) / 8) * Real.exp (-(3 / 2) * t)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hprod (by norm_num only)

/-- At |t|≥16 the Gamma norm multiplied by 1+t² is below 1/40000.
Euler reflection bounds it by 3 exp(-3|t|/2); the polynomial-exponential comparison
and the rational endpoint gate finish the uniform tail estimate. -/
theorem scaled_Gamma_half_add_I_lt_of_abs_ge_sixteen {t : ℝ} (ht : 16 ≤ |t|) :
    (1 + t ^ 2) * ‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t)‖ < 1 / 40000 := by
  have hsqrt : Real.sqrt (2 * Real.pi) ≤ 3 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num only, by linarith only [Real.pi_lt_four]⟩
  have hr : Real.exp (-|Real.pi * t| / 2) ≤ Real.exp (-(3 / 2) * |t|) := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    exact Real.exp_le_exp.mpr (by nlinarith only [Real.pi_gt_three, abs_nonneg t])
  have hb : ‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t)‖ ≤ 3 * Real.exp (-(3 / 2) * |t|) :=
    (norm_Gamma_half_add_I_le_exp t).trans
      (mul_le_mul hsqrt hr (Real.exp_pos _).le (by norm_num only))
  have hp : 0 ≤ 1 + t ^ 2 := add_nonneg (by norm_num only) (sq_nonneg t)
  have hm := mul_le_mul_of_nonneg_left hb hp
  have he :=
    mul_le_mul_of_nonneg_left (gammaResolvent_scaled_exp_tail ht) (by norm_num only : (0 : ℝ) ≤ 3)
  rw [sq_abs] at he
  calc
    _ ≤ (1 + t ^ 2) * (3 * Real.exp (-(3 / 2) * |t|)) := hm
    _ = 3 * ((1 + t ^ 2) * Real.exp (-(3 / 2) * |t|)) := by ring
    _ ≤ 3 * (257 * Real.exp (-24)) := he
    _ = 771 * Real.exp (-24) := by ring
    _ < _ := gammaResolvent_exp_tail_gate

end PseudoPrime.Analysis
