/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaResolventCertificate
public import PseudoPrime.Analysis.GammaCriticalLine
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Tactic

/-! # Gamma resolvent domination outside the compact certificate interval

A positive shifted polynomial certifies the rational tail. Exponential decay of the
Gamma function then proves strict domination for every ordinate of absolute value at least 16.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Product of the eight nonzero-weight resolvent denominators after the shift t² = 256+v.
Each factor is positive when v is nonnegative; clearing this product preserves inequalities. -/
private noncomputable def gammaResolventTailDenominator (v : ℝ) : ℝ :=
  (v + 102521 / 400) * (v + 6416 / 25) * (v + 257) * (v + 25889 / 100) * (v + 26129 / 100) *
    (v + 6656 / 25) *
    (v + 1105 / 4) *
    (v + 305)

/-- Exact shifted numerator of D(v)((1+t²)g(t)-1/40000), with t²=256+v.
All nine rational coefficients are positive. This polynomial certifies the entire tail. -/
private noncomputable def gammaResolventTailPolynomial (v : ℝ) : ℝ :=
  (76277113601902963304763227788093 / 390625000000000 : ℝ) +
    (1402441690973268381882593965912179 / 250000000000000000 : ℝ) * v ^ 1 +
    (69008322389729256463867772080547 / 1000000000000000000 : ℝ) * v ^ 2 +
    (58900955600711549955978995219 / 125000000000000000 : ℝ) * v ^ 3 +
    (385798506767837936856371163 / 200000000000000000 : ℝ) * v ^ 4 +
    (18941040900330114070871 / 4000000000000000 : ℝ) * v ^ 5 +
    (129163008438599753 / 20000000000000 : ℝ) * v ^ 6 +
    (1514907016671 / 400000000000 : ℝ) * v ^ 7 +
    (50023 / 2000000000 : ℝ) * v ^ 8

/-- For a nonnegative shift v=t²-256, clearing the resolvent denominators yields the
explicit degree-eight polynomial. Rational normalization and a ring identity verify every
coefficient; no numerical approximation or external certificate is trusted. -/
private theorem gammaResolvent_tail_identity (t : ℝ) (v : ℝ) (ht : t ^ 2 = 256 + v) (hv : 0 ≤ v) :
    gammaResolventTailDenominator v * ((1 + t ^ 2) * gammaResolventMajorant t - 1 / 40000) =
      gammaResolventTailPolynomial v := by
  simp only [gammaResolventMajorant, gammaResolventCoefficients, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  rw [ht]
  norm_num only
  dsimp only [gammaResolventTailDenominator, gammaResolventTailPolynomial]
  have h0 : (49 + (256 + v) : ℝ) ≠ 0 := ne_of_gt (by linarith only [hv])
  have h1 : (81 + 4 * (256 + v) : ℝ) ≠ 0 := ne_of_gt (by linarith only [hv])
  have h2 : (256 + 25 * (256 + v) : ℝ) ≠ 0 := ne_of_gt (by linarith only [hv])
  have h3 : (529 + 100 * (256 + v) : ℝ) ≠ 0 := ne_of_gt (by linarith only [hv])
  have h4 : (289 + 100 * (256 + v) : ℝ) ≠ 0 := ne_of_gt (by linarith only [hv])
  have h5 : (169 + 100 * (256 + v) : ℝ) ≠ 0 := ne_of_gt (by linarith only [hv])
  have h6 : (1 + (256 + v) : ℝ) ≠ 0 := ne_of_gt (by linarith only [hv])
  have h7 : (16 + 25 * (256 + v) : ℝ) ≠ 0 := ne_of_gt (by linarith only [hv])
  have h8 : (169 + 400 * (256 + v) : ℝ) ≠ 0 := ne_of_gt (by linarith only [hv])
  have h9 : (121 + 400 * (256 + v) : ℝ) ≠ 0 := ne_of_gt (by linarith only [hv])
  field_simp (discharger :=
    (first
      | (norm_num only; done)
      | (exact h0)
      | (exact h1)
      | (exact h2)
      | (exact h3)
      | (exact h4)
      | (exact h5)
      | (exact h6)
      | (exact h7)
      | (exact h8)
      | (exact h9)))
  ring

/-- At nonnegative v all eight shifted denominators are positive, so their product is
positive. This permits division in the rational tail comparison. -/
private theorem gammaResolvent_tail_denominator_pos {v : ℝ} (hv : 0 ≤ v) :
    0 < gammaResolventTailDenominator v := by
  dsimp only [gammaResolventTailDenominator]
  repeat' apply mul_pos
  all_goals exact add_pos_of_nonneg_of_pos hv (by norm_num only)

/-- At nonnegative v the shifted polynomial is strictly positive: its constant coefficient
is positive and all remaining coefficient-times-power terms are nonnegative. -/
private theorem gammaResolvent_tail_polynomial_pos {v : ℝ} (hv : 0 ≤ v) :
    0 < gammaResolventTailPolynomial v := by
  dsimp only [gammaResolventTailPolynomial]
  repeat' apply add_pos_of_pos_of_nonneg
  · norm_num only
  all_goals exact mul_nonneg (by norm_num only) (pow_nonneg hv _)

/-- If t²≥256, the scaled signed resolvent (1+t²)g(t) exceeds 1/40000.
Use the shifted polynomial identity and positivity of its denominator and numerator.
This lower bound supplies the rational side of Gamma domination on the tail. -/
theorem gammaResolvent_scaled_gt_of_sq_ge_256 {t : ℝ} (ht : 256 ≤ t ^ 2) :
    (1 / 40000 : ℝ) < (1 + t ^ 2) * gammaResolventMajorant t := by
  have hv : 0 ≤ t ^ 2 - 256 := sub_nonneg.mpr ht
  have he := gammaResolvent_tail_identity t (t ^ 2 - 256) (by ring) hv
  have hd := gammaResolvent_tail_denominator_pos hv
  have hp := gammaResolvent_tail_polynomial_pos hv
  have hm : 0 < (1 + t ^ 2) * gammaResolventMajorant t - 1 / 40000 :=
    (mul_pos_iff_of_pos_left hd).mp (he.symm ▸ hp)
  exact sub_pos.mp hm

/-- The endpoint exponential error 771 exp(-24) is below 1/40000.
A rational lower bound 5/2 for exp(1), raised to the twenty-fourth power, proves the gate. -/
private theorem gammaResolvent_exp_tail_gate : (771 : ℝ) * Real.exp (-24) < 1 / 40000 := by
  have he : (5 / 2 : ℝ) < Real.exp 1 := by linarith only [Real.exp_one_gt_d9]
  have hp : (5 / 2 : ℝ) ^ 24 < Real.exp 24 := by
    rw [show (24 : ℝ) = (24 : ℕ) * 1 by norm_num only, Real.exp_nat_mul]
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

/-- At every |t|≥16 the signed rational resolvent strictly dominates the Gamma norm
on the line Re s=1/2. Compare their scaled bounds and cancel the positive factor 1+t².
Only the compact interval remains for the global Gamma majorant certificate. -/
theorem norm_Gamma_half_add_I_lt_gammaResolvent_of_abs_ge_sixteen {t : ℝ} (ht : 16 ≤ |t|) :
    ‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t)‖ < gammaResolventMajorant t := by
  have hs : (256 : ℝ) ≤ t ^ 2 := by nlinarith only [ht, sq_abs t]
  have h :=
    (scaled_Gamma_half_add_I_lt_of_abs_ge_sixteen ht).trans
      (gammaResolvent_scaled_gt_of_sq_ge_256 hs)
  exact (mul_lt_mul_iff_right₀ (by nlinarith only [sq_nonneg t] : 0 < 1 + t ^ 2)).mp h

/-- A Gamma domination certificate on |t|≤16 extends to every real ordinate.
The rational and exponential tail estimates supply the complementary interval,
so the zero-mass comparison only needs the compact certificate as input. -/
theorem norm_Gamma_half_add_I_le_gammaResolvent_of_compact
    (h :
      ∀ t : ℝ, |t| ≤ 16 → ‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t)‖ ≤ gammaResolventMajorant t)
    (t : ℝ) : ‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t)‖ ≤ gammaResolventMajorant t := by
  by_cases ht : |t| ≤ 16
  · exact h t ht
  · exact (norm_Gamma_half_add_I_lt_gammaResolvent_of_abs_ge_sixteen (le_of_not_ge ht)).le

end PseudoPrime.Analysis
