/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiEnvelopeMain20
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiEnvelopePoly20
import PseudoPrime.Analysis.LogTaylorBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-! # Uniform remainder for the height-20 ψ envelope -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- For `L ≥ 20`, a cubic polynomial bounds the coefficient of the
exponential remainder in the `L/4` smoothing envelope. Bounds for the
logarithms and π preserve enough of the negative quadratic coefficient. -/
private theorem envelope20_remainder_coefficient {L : ℝ} (hL : 20 ≤ L) :
    let q := L / 4
    let a := L / 2 - Real.log (Real.pi * L / 4)
    q * ((a ^ 2 + 2 * a + 2) / (2 * Real.pi) + 1 / 25) + Real.log (2 * Real.pi) ≤
      L / 4 * (((L / 2 - 11 / 4) ^ 2 + 2 * (L / 2 - 11 / 4) + 2) / (2 * (157 / 50)) + 1 / 25) +
        46 / 25 := by
  dsimp only
  let q := L / 4
  let a := L / 2 - Real.log (Real.pi * L / 4)
  let u := L / 2 - 11 / 4
  have hL0 : 0 < L := by linarith only [hL]
  have hq0 : 0 ≤ q := by
    dsimp only [q]; linarith only [hL]
  have hlogupper : Real.log (Real.pi * L / 4) ≤ Real.log L := by
    apply Real.log_le_log
    · exact div_pos (mul_pos Real.pi_pos hL0) (by norm_num only)
    · nlinarith only [Real.pi_lt_four, hL0]
  have ha0 : 0 ≤ a := by
    dsimp only [a]
    have hh := (log_bounds_20 hL).2
    linarith only [hh, hlogupper, hL]
  have hcert :=
    Analysis.rationalLogIntervalCheck_sound
      (show
        Analysis.rationalLogIntervalCheck (31415 / 2000) 4 64 (275413 / 100000) (275415 / 100000) =
          true
        from by decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hcert
  have hpi : (31415 / 10000 : ℝ) ≤ Real.pi := by linarith only [Real.pi_gt_d4]
  have harg : (31415 / 2000 : ℝ) ≤ Real.pi * L / 4 := by nlinarith only [hpi, hL, Real.pi_pos]
  have hloglower : (11 / 4 : ℝ) ≤ Real.log (Real.pi * L / 4) := by
    have h := Real.log_le_log (by norm_num only : (0 : ℝ) < 31415 / 2000) harg
    linarith only [h, hcert.1]
  have hau : a ≤ u := by
    dsimp only [a, u]; linarith only [hloglower]
  have hu0 : 0 ≤ u := by
    dsimp only [u]; linarith only [hL]
  have hasq := mul_le_mul hau hau ha0 hu0
  have hnum : 0 ≤ a ^ 2 + 2 * a + 2 := by nlinarith only [sq_nonneg a, ha0]
  have hden : (1 / (2 * Real.pi) : ℝ) ≤ 1 / (2 * (157 / 50)) := by
    apply (div_le_div_iff₀ (by nlinarith only [Real.pi_pos]) (by norm_num only)).2
    nlinarith only [Real.pi_gt_d4]
  have hB1 := mul_le_mul_of_nonneg_left hden hnum
  have hB :
    (a ^ 2 + 2 * a + 2) / (2 * Real.pi) + 1 / 25 ≤
      (u ^ 2 + 2 * u + 2) / (2 * (157 / 50)) + 1 / 25 := by
    simp only [div_eq_mul_inv] at hB1 ⊢
    nlinarith only [hB1, hasq, hau]
  have hmul := mul_le_mul_of_nonneg_left hB hq0
  have hc : Real.log (2 * Real.pi) ≤ 46 / 25 := by
    have h8 :=
      Analysis.rationalLogIntervalCheck_sound
        (show
          Analysis.rationalLogIntervalCheck (62832 / 10000) 2 64 (1837 / 1000) (1838 / 1000) = true
          from by decide +kernel)
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h8
    have hp' : (2 * Real.pi : ℝ) ≤ 62832 / 10000 := by linarith only [Real.pi_lt_d4]
    have hl' := Real.log_le_log (by nlinarith only [Real.pi_pos] : (0 : ℝ) < 2 * Real.pi) hp'
    linarith only [hl', h8.2]
  change
    q * ((a ^ 2 + 2 * a + 2) / (2 * Real.pi) + 1 / 25) + Real.log (2 * Real.pi) ≤
      q * ((u ^ 2 + 2 * u + 2) / (2 * (157 / 50)) + 1 / 25) + 46 / 25
  linarith only [hmul, hc]

/-- For `L ≥ 20`, the remainder in the `L/4` smoothing envelope is at most
`3/1000`. Its coefficient is bounded by a cubic polynomial whose product
with `exp(-L/2)` decreases from the endpoint. -/
theorem envelope20_remainder_le {L : ℝ} (hL : 20 ≤ L) :
    let s := Real.exp (L / 2)
    let q := L / 4
    let a := L / 2 - Real.log (Real.pi * L / 4)
    q / s * ((a ^ 2 + 2 * a + 2) / (2 * Real.pi) + 1 / 25) + Real.log (2 * Real.pi) / s +
        1 / (q * Real.exp L) ≤
      3 / 1000 := by
  dsimp only
  let s := Real.exp (L / 2)
  let q := L / 4
  let a := L / 2 - Real.log (Real.pi * L / 4)
  change
    q / s * ((a ^ 2 + 2 * a + 2) / (2 * Real.pi) + 1 / 25) + Real.log (2 * Real.pi) / s +
        1 / (q * Real.exp L) ≤
      3 / 1000
  have hq5 : 5 ≤ q := by
    dsimp only [q]; linarith only [hL]
  have hqpos : 0 < q := by linarith only [hq5]
  have hqinv : q⁻¹ ≤ (1 / 5 : ℝ) := by
    simpa only [one_div] using (inv_le_inv₀ hqpos (by norm_num only : (0 : ℝ) < 5)).2 hq5
  have hcoef := envelope20_remainder_coefficient hL
  change
    q * ((a ^ 2 + 2 * a + 2) / (2 * Real.pi) + 1 / 25) + Real.log (2 * Real.pi) ≤
      L / 4 * (((L / 2 - 11 / 4) ^ 2 + 2 * (L / 2 - 11 / 4) + 2) / (2 * (157 / 50)) + 1 / 25) +
        46 / 25 at hcoef
  have hm := mul_le_mul_of_nonneg_right hcoef (Real.exp_pos (-L / 2)).le
  have hqterm := mul_le_mul_of_nonneg_right hqinv (Real.exp_pos (-L)).le
  have hpoly := envelope_poly20_bound hL
  have hpoly_eq :
    L / 4 * (((L / 2 - 11 / 4) ^ 2 + 2 * (L / 2 - 11 / 4) + 2) / (2 * (157 / 50)) + 1 / 25) +
        46 / 25 =
      25 * L ^ 3 / 2512 - 175 * L ^ 2 / 2512 + 43137 * L / 251200 + 46 / 25 := by
    ring
  rw [hpoly_eq] at hm
  have hes : Real.exp (-L / 2) = s⁻¹ := by
    change Real.exp (-L / 2) = (Real.exp (L / 2))⁻¹
    rw [show -L / 2 = -(L / 2) by ring, Real.exp_neg]
  have heL : Real.exp (-L) = (Real.exp L)⁻¹ := Real.exp_neg L
  rw [hes] at hm hpoly
  rw [heL] at hqterm hpoly
  simp only [div_eq_mul_inv, mul_inv_rev] at hm hqterm hpoly ⊢
  nlinarith only [hm, hqterm, hpoly]

/-- For `L ≥ 20`, the `L/4` combined-zero envelope lies below the
Lee–Nosal normalized target by at least `1/150`. The uniform main-term gap
exceeds `1/100`, while the remainder is at most `3/1000`. -/
theorem envelope20_le_target {L : ℝ} (hL : 20 ≤ L) :
    let s := Real.exp (L / 2)
    let q := L / 4
    let a := L / 2 - Real.log (Real.pi * L / 4)
    q / 2 + Real.log (2 * Real.pi) / s +
        (1 + q / s) * ((a ^ 2 + 2 * a + 2) / (2 * Real.pi) + 1 / 25) +
        1 / (q * Real.exp L) ≤
      L * (L - Real.log L) / (8 * Real.pi) - 1 / 150 := by
  dsimp only
  let s := Real.exp (L / 2)
  let q := L / 4
  let a := L / 2 - Real.log (Real.pi * L / 4)
  change
    q / 2 + Real.log (2 * Real.pi) / s +
        (1 + q / s) * ((a ^ 2 + 2 * a + 2) / (2 * Real.pi) + 1 / 25) +
        1 / (q * Real.exp L) ≤
      L * (L - Real.log L) / (8 * Real.pi) - 1 / 150
  have hrem := envelope20_remainder_le hL
  change
    q / s * ((a ^ 2 + 2 * a + 2) / (2 * Real.pi) + 1 / 25) + Real.log (2 * Real.pi) / s +
        1 / (q * Real.exp L) ≤
      3 / 1000 at hrem
  have hmain := envelope20_main_gap_uniform hL
  change
    (1 / 100 : ℝ) <
      (L * (L - Real.log L) - Real.pi * L - 4 * (a ^ 2 + 2 * a + 2) - (8 / 25 : ℝ) * Real.pi) /
        (8 * Real.pi) at hmain
  have heq :
    (L * (L - Real.log L) - Real.pi * L - 4 * (a ^ 2 + 2 * a + 2) - (8 / 25 : ℝ) * Real.pi) /
        (8 * Real.pi) =
      L * (L - Real.log L) / (8 * Real.pi) - q / 2 -
        ((a ^ 2 + 2 * a + 2) / (2 * Real.pi) + 1 / 25) := by
    dsimp only [q]
    have hp := mul_inv_cancel₀ Real.pi_ne_zero
    simp only [div_eq_mul_inv, mul_inv_rev]
    linear_combination (-(L / 8 + 1 / 25)) * hp
  rw [heq] at hmain
  nlinarith only [hrem, hmain]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
