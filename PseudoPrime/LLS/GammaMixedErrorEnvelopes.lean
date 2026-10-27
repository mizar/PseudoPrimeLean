/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaMixedProfileSeparation

/-! # Reusable scalar cell envelopes for all non-Euler profile errors -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Input: rational root endpoints and a logarithm cap.
Definition: the explicit linear plus reciprocal-root ramp envelope.
Output: a rational allowance. Role: certify uniform ramp costs by finite arithmetic. -/
def gammaRampCellRationalUpper (rlo rhi ell : ℚ) : ℚ :=
  (42 / 494) * (11 / 200) * rhi + (3 / 2) * (63 / 800) + (42 / 494) * 101 * (2 / 25) +
    ((3 / 2) + (42 / 494) * 101) * ((1839 / 1000) * ell + 21 / 20) / rlo

/-- Input: rational root endpoints and a logarithm cap.
Definition: the principal numerator at upper endpoints divided by the lower root.
Output: a rational allowance. Role: check principal errors numerically. -/
def gammaPrincipalCellRationalUpper (rlo rhi ell : ℚ) : ℚ :=
  (rhi / 8 + (1839 / 1000) * (2 * ell + 3) + 21 / 10) / rlo

/-- Input: a positive scale, positive lower root, root enclosures and nonnegative common log cap.
Claim: the paired ramp error is below a scalar endpoint envelope.
Proof: retain x=(sqrt x)^2 and compare linear, quadratic and reciprocal-root terms separately.
Role: avoid a new nonlinear analytic proof for every logarithmic cell. -/
theorem gamma_ramp_error_le_cell_envelope {x rlo rhi ell : ℝ} (hx : 0 < x) (hlo : 0 < rlo)
    (hrlo : rlo ≤ Real.sqrt x) (hrhi : Real.sqrt x ≤ rhi) (hell : 0 ≤ ell)
    (hext : Real.log ((101 / 40 : ℝ) * x) ≤ ell) (hramp : Real.log (x * (99 / 40)) ≤ ell) :
    gammaRampPairedErrorNumerator x / Real.sqrt x ≤
      (42 / 494 : ℝ) * (11 / 200) * rhi + (3 / 2) * (63 / 800) + (42 / 494) * 101 * (2 / 25) +
        ((3 / 2) + (42 / 494) * 101) * ((1839 / 1000) * ell + 21 / 20) / rlo := by
  let A : ℝ := (42 / 494) * (11 / 200)
  let B : ℝ := (3 / 2) * (63 / 800) + (42 / 494) * 101 * (2 / 25)
  let C : ℝ := ((3 / 2) + (42 / 494) * 101) * ((1839 / 1000) * ell + 21 / 20)
  have hC0 : 0 ≤ C := by
    dsimp only [C]; linarith only [hell]
  have hN : gammaRampPairedErrorNumerator x ≤ A * (Real.sqrt x) ^ 2 + B * Real.sqrt x + C := by
    unfold gammaRampPairedErrorNumerator rampSmoothedIncrementError rampExtendedSmoothedError
    dsimp only [A, B, C]
    nlinarith only [hext, hramp, Real.sq_sqrt hx.le]
  have hprod := mul_le_mul_of_nonneg_left hrhi (Real.sqrt_nonneg x)
  have hA := mul_le_mul_of_nonneg_left hprod (show (0 : ℝ) ≤ A by norm_num only [A])
  have hC := mul_le_mul_of_nonneg_left hrlo (div_nonneg hC0 hlo.le)
  rw [div_mul_cancel₀ C hlo.ne'] at hC
  rw [div_le_iff₀ (Real.sqrt_pos.mpr hx)]
  dsimp only [A, B, C] at hN hA hC
  nlinarith only [hN, hA, hC]

/-- Input: positive lower root, root enclosures and a nonnegative log cap.
Claim: the principal error is below the displayed fixed cell envelope.
Proof: compare the numerator above and the denominator below.
Role: expose one rational numerical check for the entire principal-error cell. -/
theorem gamma_principal_error_le_cell_envelope {x rlo rhi ell : ℝ} (hlo : 0 < rlo)
    (hrlo : rlo ≤ Real.sqrt x) (hrhi : Real.sqrt x ≤ rhi) (hell : 0 ≤ ell)
    (hlog : Real.log x ≤ ell) :
    (Real.sqrt x / 8 + (1839 / 1000 : ℝ) * (2 * Real.log x + 3) + 21 / 10) / Real.sqrt x ≤
      (rhi / 8 + (1839 / 1000 : ℝ) * (2 * ell + 3) + 21 / 10) / rlo := by
  have hnum :
    Real.sqrt x / 8 + (1839 / 1000 : ℝ) * (2 * Real.log x + 3) + 21 / 10 ≤
      rhi / 8 + (1839 / 1000 : ℝ) * (2 * ell + 3) + 21 / 10 := by
    linarith only [hrhi, hlog]
  have hnonneg : 0 ≤ rhi / 8 + (1839 / 1000 : ℝ) * (2 * ell + 3) + 21 / 10 := by
    have hr0 := (Real.sqrt_nonneg x).trans hrhi
    linarith only [hr0, hell]
  exact
    (div_le_div_of_nonneg_right hnum (Real.sqrt_nonneg x)).trans
      (div_le_div₀ hnonneg le_rfl hlo hrlo)

/-- Input: L>=300. Claim: the quadratic-profile pole error is at most 19/10.
Proof: retain the root lower bound proportional to L before dividing.
Role: share the pole allowance on all bridge cells and larger scales. -/
theorem gamma_pole_error_le_of_threehundred_le {L : ℝ} (hL : 300 ≤ L) :
    let x := (2 / 5 : ℝ) * L ^ 2;
    ((7 / 6 : ℝ) * (L + 7 / 5) + 4) / Real.sqrt x ≤ 19 / 10 := by
  dsimp only
  have hL0 : 0 < L := by linarith only [hL]
  have hx := mul_pos (by norm_num only : (0 : ℝ) < 2 / 5) (sq_pos_of_pos hL0)
  have hr : (79 / 125 : ℝ) * L ≤ Real.sqrt ((2 / 5 : ℝ) * L ^ 2) := by
    apply (Real.le_sqrt (mul_nonneg (by norm_num only) hL0.le) hx.le).mpr
    nlinarith only [sq_nonneg L]
  rw [div_le_iff₀ (Real.sqrt_pos.mpr hx)]
  linarith only [hr, hL]

/-- Input: x>=36000. Claim: the left-line error is at most 1/8.
Proof: apply the integer-power certificate to the rational exponent.
Role: reuse a whole-half-line error bound across all bridge cells. -/
theorem gamma_left_error_le_of_scale_ge_36000 {x : ℝ} (hxlo : 36000 ≤ x) :
    43 * x ^ (-9 / 16 : ℝ) ≤ 1 / 8 := by
  have hx : 0 < x := by linarith only [hxlo]
  have hp := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 36000) hxlo 9
  have hc : (1 : ℝ) ≤ (1 / 344 : ℝ) ^ 16 * (36000 : ℝ) ^ 9 := by norm_num only
  have hd := mul_le_mul_of_nonneg_left hp (pow_nonneg (by norm_num only : (0 : ℝ) ≤ 1 / 344) 16)
  have h :=
    Analysis.rpow_neg_nat_div_le_of_power_bound hx (by norm_num only : (0 : ℝ) ≤ 1 / 344) 9 16
      (by norm_num only) (hc.trans hd)
  norm_num only [neg_div] at h ⊢
  linarith only [h]

end PseudoPrime.LLS
