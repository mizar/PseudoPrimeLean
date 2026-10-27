/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.OddEndpointLogWindow
public import PseudoPrime.LLS.OddEndpointDoubleLogRoot

/-! # A continuous odd-prime endpoint certificate at intermediate scales -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For 128<=y<=160, the window polynomial is positive at the affine level
3241y/3200+18/25+7/5. An exact quartic Bernstein identity with five positive
rational coefficients certifies the whole real interval for odd-prime extraction. -/
theorem oddMidscaleEndpoint_window_pos {y : ℝ} (hlo : 128 ≤ y) (hhi : y ≤ 160) :
    0 <
      oddEndpointLogWindowPolynomial ((3241 / 3200 : ℝ) * y + 18 / 25 + 7 / 5) (2096 / 1831) y
        ((2231 / 320000) * y + 9899 / 2500) (y / 144 + 397 / 100) (7 / 10) := by
  have ht₀ : 0 ≤ (y - 128) / 32 := by linarith only [hlo]
  have ht₁ : (y - 128) / 32 ≤ 1 := by linarith only [hhi]
  have hp :=
    Analysis.bernsteinQuartic_pos (c₀ := (1503236186126893 / 23173593750 : ℝ)) (c₁ :=
      (1227361863780816379 / 14831100000000 : ℝ)) (c₂ := (2395107382922781553 / 22246650000000 : ℝ))
      (c₃ := (140850051216944447 / 988740000000 : ℝ)) (c₄ := (15746043691850599 / 82395000000 : ℝ))
      (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      ht₀ ht₁
  convert hp using 1
  dsimp only [oddEndpointLogWindowPolynomial, fullEndpointPolynomial, Analysis.bernsteinQuartic]
  ring

/-- On 128<=y<=160, the indicated rational chord and tangent enclose log y.
Use logarithmic concavity at 128 and 160 and the tangent at 144, with
certified elementary logarithm bounds. This supplies the window inputs. -/
theorem oddMidscaleEndpoint_log_window {y : ℝ} (hlo : 128 ≤ y) (hhi : y ≤ 160) :
    (2231 / 320000 : ℝ) * y + 9899 / 2500 ≤ Real.log y ∧ Real.log y ≤ y / 144 + 397 / 100 := by
  have h128 : (4852 / 1000 : ℝ) ≤ Real.log 128 := by
    rw [show (128 : ℝ) = 2 ^ 7 by norm_num only, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [Real.log_two_gt_d9]
  have h160 : (50751 / 10000 : ℝ) ≤ Real.log 160 := by
    rw [show (160 : ℝ) = 2 ^ 5 * 5 by norm_num only,
      Real.log_mul (by norm_num only) (by norm_num only), Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [Real.log_two_gt_d9, Real.log_five_gt_d9]
  have h144 : Real.log (144 : ℝ) ≤ 497 / 100 := by
    rw [show (144 : ℝ) = 2 ^ 4 * 3 ^ 2 by norm_num only,
      Real.log_mul (by norm_num only) (by norm_num only), Real.log_pow, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [Real.log_two_lt_d9, Real.log_three_lt_d9]
  have ht :=
    Real.log_le_sub_one_of_pos
      (div_pos (by linarith only [hlo] : 0 < y) (by norm_num only : (0 : ℝ) < 144))
  rw [Real.log_div (by linarith only [hlo] : y ≠ 0) (by norm_num only : (144 : ℝ) ≠ 0)] at ht
  constructor
  · exact
      log_chord_le_of_endpoints (by norm_num only : (0 : ℝ) < 128)
        (by norm_num only : (128 : ℝ) < 160) hlo hhi (by linarith only [h128])
        (by linarith only [h160])
  · linarith only [ht, h144]

/-- For 128<=y<=160, the zero-at-two branch polynomial is positive at the
affine ambient level. Apply the generic two-sided logarithm window comparison
to the exact Bernstein certificate. This retains both odd-prime costs. -/
theorem oddMidscaleEndpoint_zero_pos {y : ℝ} (hlo : 128 ≤ y) (hhi : y ≤ 160) :
    0 <
      oddEndpointTwoCostPolynomial ((3241 / 3200 : ℝ) * y + 18 / 25 + 7 / 5) (2096 / 1831) y
        (Real.log y) (7 / 10) (2 * (Real.log y) ^ 2) := by
  have hw := oddMidscaleEndpoint_log_window hlo hhi
  exact
    (oddMidscaleEndpoint_window_pos hlo hhi).trans_le
      (oddEndpointLogWindowPolynomial_le (by linarith only [hlo]) (by linarith only [hlo])
        (by norm_num only) (by norm_num only) (by linarith only [hlo]) hw.1 hw.2)

end PseudoPrime.LLS.PaperStatements
