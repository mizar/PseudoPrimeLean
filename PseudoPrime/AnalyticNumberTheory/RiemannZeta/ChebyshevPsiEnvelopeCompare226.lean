/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiEnvelopeMain226
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiEnvelopeRemainder226
import PseudoPrime.Analysis.LogTaylorBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-! # Comparison of the high-range Chebyshev envelope -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- At `L ≥ 113/5`, the coefficient of `exp(-L/2)` in the envelope
remainder is bounded by the displayed cubic polynomial. Elementary bounds
for the logarithm, π and the chosen smoothing scale give the comparison. -/
private theorem envelope226_remainder_coefficient {L : ℝ} (hL : (113 / 5 : ℝ) ≤ L) :
    let q := 5 * L / (6 * Real.pi)
    let a := L / 2 - Real.log (5 * L / 6)
    q * ((a ^ 2 + 2 * a + 2) / (2 * Real.pi) + 2 / 5) + Real.log (2 * Real.pi) ≤
      5 * L ^ 3 / 432 + 5 * L ^ 2 / 108 + 11 * L / 54 + 2 := by
  dsimp only
  let q := 5 * L / (6 * Real.pi)
  let a := L / 2 - Real.log (5 * L / 6)
  have hL0 : 0 < L := by linarith only [hL]
  have hp : 0 < 6 * Real.pi := by nlinarith only [Real.pi_pos]
  have hq0 : 0 ≤ q := (div_pos (by linarith only [hL]) hp).le
  have hq : q ≤ 5 * L / 18 := by
    dsimp only [q]
    apply (div_le_div_iff₀ hp (by norm_num only : (0 : ℝ) < 18)).2
    nlinarith only [Real.pi_gt_three, hL0]
  have hlogpos : 0 ≤ Real.log (5 * L / 6) := by
    apply Real.log_nonneg
    linarith only [hL]
  have hlogupper : Real.log (5 * L / 6) ≤ Real.log L := by
    apply Real.log_le_log
    · linarith only [hL]
    · linarith only [hL]
  have ha0 : 0 ≤ a := by
    dsimp only [a]
    have hh := (log_bounds_226 hL).2
    linarith only [hh, hlogupper, hL]
  have ha1 : a ≤ L / 2 := by
    dsimp only [a]
    linarith only [hlogpos]
  have ha2 := mul_le_mul ha1 ha1 ha0 (by linarith only [hL])
  have hinv : 1 / (2 * Real.pi) ≤ (1 / 6 : ℝ) := by
    apply (div_le_iff₀ (by nlinarith only [Real.pi_pos] : 0 < 2 * Real.pi)).2
    nlinarith only [Real.pi_gt_three]
  have hnum : 0 ≤ a ^ 2 + 2 * a + 2 := by nlinarith only [sq_nonneg a, ha0]
  have hB1 := mul_le_mul_of_nonneg_left hinv hnum
  have hB : (a ^ 2 + 2 * a + 2) / (2 * Real.pi) + 2 / 5 ≤ L ^ 2 / 24 + L / 6 + 11 / 15 := by
    simp only [div_eq_mul_inv] at hB1 ⊢
    nlinarith only [hB1, ha1, ha2]
  have hB0 : 0 ≤ (a ^ 2 + 2 * a + 2) / (2 * Real.pi) + 2 / 5 := by
    have hd := div_nonneg hnum (by nlinarith only [Real.pi_pos] : 0 ≤ 2 * Real.pi)
    linarith only [hd]
  have hmul := mul_le_mul hq hB hB0 (by linarith only [hq, hq0])
  have hc : Real.log (2 * Real.pi) ≤ 2 := by
    have h8 :=
      Analysis.rationalLogIntervalCheck_sound
        (show
          Analysis.rationalLogIntervalCheck (62832 / 10000) 2 64 (1837 / 1000) (1838 / 1000) = true
          from by decide +kernel)
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h8
    have hp' : (2 * Real.pi : ℝ) ≤ 62832 / 10000 := by linarith only [Real.pi_lt_d4]
    have hl' := Real.log_le_log (by nlinarith only [Real.pi_pos] : (0 : ℝ) < 2 * Real.pi) hp'
    linarith only [hl', h8.2]
  nlinarith only [hmul, hc]

/-- For `L ≥ 113/5`, the nonnegative remainder in the combined-zero
Chebyshev envelope is at most `21/10000`. A cubic coefficient bound and
monotonicity of its exponential factors give the uniform estimate. -/
theorem envelope226_remainder_le {L : ℝ} (hL : (113 / 5 : ℝ) ≤ L) :
    let s := Real.exp (L / 2)
    let q := 5 * L / (6 * Real.pi)
    let a := L / 2 - Real.log (5 * L / 6)
    q / s * ((a ^ 2 + 2 * a + 2) / (2 * Real.pi) + 2 / 5) + Real.log (2 * Real.pi) / s +
        1 / (q * Real.exp L) ≤
      21 / 10000 := by
  dsimp only
  let s := Real.exp (L / 2)
  let q := 5 * L / (6 * Real.pi)
  let a := L / 2 - Real.log (5 * L / 6)
  change
    q / s * ((a ^ 2 + 2 * a + 2) / (2 * Real.pi) + 2 / 5) + Real.log (2 * Real.pi) / s +
        1 / (q * Real.exp L) ≤
      21 / 10000
  have hp : 0 < 6 * Real.pi := by nlinarith only [Real.pi_pos]
  have hq5 : 5 ≤ q := by
    dsimp only [q]
    apply (le_div_iff₀ hp).2
    nlinarith only [hL, Real.pi_lt_d4]
  have hqpos : 0 < q := by linarith only [hq5]
  have hqinv : q⁻¹ ≤ (1 / 5 : ℝ) := by
    simpa only [one_div] using (inv_le_inv₀ hqpos (by norm_num only : (0 : ℝ) < 5)).2 hq5
  have hcoef := envelope226_remainder_coefficient hL
  change
    q * ((a ^ 2 + 2 * a + 2) / (2 * Real.pi) + 2 / 5) + Real.log (2 * Real.pi) ≤
      5 * L ^ 3 / 432 + 5 * L ^ 2 / 108 + 11 * L / 54 + 2 at hcoef
  have hm := mul_le_mul_of_nonneg_right hcoef (Real.exp_pos (-L / 2)).le
  have hqterm := mul_le_mul_of_nonneg_right hqinv (Real.exp_pos (-L)).le
  have hpoly := envelope226_remainder_bound hL
  have hes : Real.exp (-L / 2) = s⁻¹ := by
    change Real.exp (-L / 2) = (Real.exp (L / 2))⁻¹
    rw [show -L / 2 = -(L / 2) by ring, Real.exp_neg]
  have heL : Real.exp (-L) = (Real.exp L)⁻¹ := Real.exp_neg L
  rw [hes] at hm hpoly
  rw [heL] at hqterm hpoly
  simp only [div_eq_mul_inv, mul_inv_rev] at hm hqterm hpoly ⊢
  nlinarith only [hm, hqterm, hpoly]

/-- For `L ≥ 113/5`, the combined-zero envelope is below the normalized
Lee–Nosal target by at least `1/300`. The uniform main gap exceeds the
independently bounded exponential remainder. -/
theorem envelope226_le_target {L : ℝ} (hL : (113 / 5 : ℝ) ≤ L) :
    let s := Real.exp (L / 2)
    let q := 5 * L / (6 * Real.pi)
    let a := L / 2 - Real.log (5 * L / 6)
    q / 2 + Real.log (2 * Real.pi) / s +
        (1 + q / s) * ((a ^ 2 + 2 * a + 2) / (2 * Real.pi) + 2 / 5) +
        1 / (q * Real.exp L) ≤
      L * (L - Real.log L) / (8 * Real.pi) - 1 / 300 := by
  dsimp only
  let s := Real.exp (L / 2)
  let q := 5 * L / (6 * Real.pi)
  let a := L / 2 - Real.log (5 * L / 6)
  change
    q / 2 + Real.log (2 * Real.pi) / s +
        (1 + q / s) * ((a ^ 2 + 2 * a + 2) / (2 * Real.pi) + 2 / 5) +
        1 / (q * Real.exp L) ≤
      L * (L - Real.log L) / (8 * Real.pi) - 1 / 300
  have hrem := envelope226_remainder_le hL
  change
    q / s * ((a ^ 2 + 2 * a + 2) / (2 * Real.pi) + 2 / 5) + Real.log (2 * Real.pi) / s +
        1 / (q * Real.exp L) ≤
      21 / 10000 at hrem
  have hmain := envelope226_main_gap_uniform hL
  change
    (11 / 2000 : ℝ) <
      (L * (L - Real.log L) - (10 / 3 : ℝ) * L - 4 * (a ^ 2 + 2 * a + 2) - (16 / 5 : ℝ) * Real.pi) /
        (8 * Real.pi) at hmain
  have heq :
    (L * (L - Real.log L) - (10 / 3 : ℝ) * L - 4 * (a ^ 2 + 2 * a + 2) - (16 / 5 : ℝ) * Real.pi) /
        (8 * Real.pi) =
      L * (L - Real.log L) / (8 * Real.pi) - q / 2 -
        ((a ^ 2 + 2 * a + 2) / (2 * Real.pi) + 2 / 5) := by
    dsimp only [q]
    have hp := mul_inv_cancel₀ Real.pi_ne_zero
    simp only [div_eq_mul_inv, mul_inv_rev]
    linear_combination (-(2 / 5 : ℝ)) * hp
  rw [heq] at hmain
  nlinarith only [hrem, hmain]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
