/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.LogLinearAnchor
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Tactic.NormNum

/-! # Selected logarithmic budgets for non-one Gamma witnesses -/

@[expose] public section

namespace PseudoPrime.LLS

/-- For every L ≥ 30000, log L ≤ L/2800. Compare the anchor with 2^15,
use the certified log two upper bound, then apply the real-anchor tangent lemma.
This controls the non-one cutoff logarithm on a full half-line. -/
theorem conductor_free_nonOne_log_bound {L : ℝ} (hL : 30000 ≤ L) : Real.log L ≤ L / 2800 := by
  have hanchor :=
    Real.log_le_log (by norm_num only : (0 : ℝ) < 30000) (by norm_num only : (30000 : ℝ) ≤ 2 ^ 15)
  rw [Real.log_pow] at hanchor
  norm_num only [Nat.cast_ofNat] at hanchor
  have h :=
    Analysis.log_le_mul_of_anchor (a := 30000) (b := 1 / 2800) (by norm_num only) hL
      (by linarith only [hanchor, Real.log_two_lt_d9]) (by norm_num only)
  simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using h

/-- At scale x=(32/99)L² with L ≥ 30000, the cutoff logarithm is at most L/1400.
Compare the coefficient-four-fifths cutoff with L² and apply the log anchor.
This supplies common bounds for the principal, ramp and prime-two errors. -/
theorem conductor_free_nonOne_cutoff_log {L : ℝ} (hL : 30000 ≤ L) :
    Real.log (((32 / 99 : ℝ) * L ^ 2) * (99 / 40)) ≤ L / 1400 := by
  have hL0 : 0 < L := by linarith only [hL]
  have hc :=
    Real.log_le_log
      (mul_pos (mul_pos (by norm_num only : (0 : ℝ) < 32 / 99) (sq_pos_of_pos hL0))
        (by norm_num only : (0 : ℝ) < 99 / 40))
      (show ((32 / 99 : ℝ) * L ^ 2) * (99 / 40) ≤ L ^ 2 by nlinarith only [sq_nonneg L])
  rw [Real.log_pow] at hc
  norm_num only [Nat.cast_ofNat] at hc
  linarith only [hc, conductor_free_nonOne_log_bound hL]

/-- For every L ≥ 1000, log L ≤ (7/1000)L. Bound the anchor by log(2^10)
and the certified log two upper value, then apply the generic real-anchor
tangent theorem. This controls every larger near-square witness scale. -/
theorem nearSquare_gamma_log_bound {L : ℝ} (hL : 1000 ≤ L) : Real.log L ≤ (7 / 1000 : ℝ) * L := by
  have ha :=
    Real.log_le_log (by norm_num only : (0 : ℝ) < 1000) (by norm_num only : (1000 : ℝ) ≤ 2 ^ 10)
  rw [Real.log_pow] at ha
  norm_num only [Nat.cast_ofNat] at ha
  exact
    Analysis.log_le_mul_of_anchor (a := 1000) (by norm_num only) hL
      (by linarith only [ha, Real.log_two_lt_d9]) (by norm_num only)

/-- For L > 0 with log L ≤ L/2800, the four-fifths cutoff logarithm is at most L/1400.
Compare the cutoff with L² and use log(L²)=2 log L. This isolates the logarithmic
hypothesis from the numerical starting point for subsequent error estimates. -/
theorem nonOne_cutoff_log_of_log_ratio {L : ℝ} (hL0 : 0 < L) (hlogL : Real.log L ≤ L / 2800) :
    Real.log (((32 / 99 : ℝ) * L ^ 2) * (99 / 40)) ≤ L / 1400 := by
  have hc :=
    Real.log_le_log
      (mul_pos (mul_pos (by norm_num only : (0 : ℝ) < 32 / 99) (sq_pos_of_pos hL0))
        (by norm_num only : (0 : ℝ) < 99 / 40))
      (show ((32 / 99 : ℝ) * L ^ 2) * (99 / 40) ≤ L ^ 2 by nlinarith only [sq_nonneg L])
  rw [Real.log_pow] at hc
  norm_num only [Nat.cast_ofNat] at hc
  linarith only [hc, hlogL]

/-- For L > 0 and log L ≤ L/2000, the four-fifths cutoff logarithm is at most L/1000.
Compare the cutoff with L² and double the logarithm bound. This weaker logarithmic
hypothesis permits smaller starting scales in the retained Euler comparison. -/
theorem nonOne_cutoff_log_of_wide_ratio {L : ℝ} (hL0 : 0 < L) (hlogL : Real.log L ≤ L / 2000) :
    Real.log (((32 / 99 : ℝ) * L ^ 2) * (99 / 40)) ≤ L / 1000 := by
  have hc :=
    Real.log_le_log
      (mul_pos (mul_pos (by norm_num only : (0 : ℝ) < 32 / 99) (sq_pos_of_pos hL0))
        (by norm_num only : (0 : ℝ) < 99 / 40))
      (show ((32 / 99 : ℝ) * L ^ 2) * (99 / 40) ≤ L ^ 2 by nlinarith only [sq_nonneg L])
  rw [Real.log_pow] at hc
  norm_num only [Nat.cast_ofNat] at hc
  linarith only [hc, hlogL]

/-- For L ≥ 29121, log L ≤ L/2800. Bound the anchor by 2^15, use the
certified logarithm of two, and extend by the logarithm tangent inequality.
This closes the logarithmic hypothesis on a full half-line. -/
theorem nonOne_log_ratio_of_ge_29121 {L : ℝ} (hL : 29121 ≤ L) : Real.log L ≤ L / 2800 := by
  have hanchor :=
    Real.log_le_log (by norm_num only : (0 : ℝ) < 29121) (by norm_num only : (29121 : ℝ) ≤ 2 ^ 15)
  rw [Real.log_pow] at hanchor
  norm_num only [Nat.cast_ofNat] at hanchor
  have h :=
    Analysis.log_le_mul_of_anchor (a := 29121) (b := 1 / 2800) (by norm_num only) hL
      (by linarith only [hanchor, Real.log_two_lt_d9]) (by norm_num only)
  simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using h

/-- For every L ≥ 22920, log L ≤ L/2000. Compare the anchor with 2^15,
use the certified logarithm of two and extend by a tangent inequality.
This discharges the logarithmic condition on a complete half-line. -/
theorem nonOne_log_ratio_of_ge_22920 {L : ℝ} (hL : 22920 ≤ L) : Real.log L ≤ L / 2000 := by
  have hanchor :=
    Real.log_le_log (by norm_num only : (0 : ℝ) < 22920) (by norm_num only : (22920 : ℝ) ≤ 2 ^ 15)
  rw [Real.log_pow] at hanchor
  norm_num only [Nat.cast_ofNat] at hanchor
  have h :=
    Analysis.log_le_mul_of_anchor (a := 22920) (b := 1 / 2000) (by norm_num only) hL
      (by linarith only [hanchor, Real.log_two_lt_d9]) (by norm_num only)
  simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using h

/-- For L ≥ 22221, log L ≤ L/2000. Bound the anchor by 2^15 and extend
with the logarithm tangent. This supplies the error condition for the even-character bound. -/
theorem nonOne_log_ratio_of_ge_22221 {L : ℝ} (hL : 22221 ≤ L) : Real.log L ≤ L / 2000 := by
  have hanchor :=
    Real.log_le_log (by norm_num only : (0 : ℝ) < 22221) (by norm_num only : (22221 : ℝ) ≤ 2 ^ 15)
  rw [Real.log_pow] at hanchor
  norm_num only [Nat.cast_ofNat] at hanchor
  have h :=
    Analysis.log_le_mul_of_anchor (a := 22221) (b := 1 / 2000) (by norm_num only) hL
      (by linarith only [hanchor, Real.log_two_lt_d9]) (by norm_num only)
  simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using h

end PseudoPrime.LLS
