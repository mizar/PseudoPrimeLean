/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaFourFifthsRetainedNumerics

/-! # Uniform coefficient-four-fifths errors for the leading Euler credit -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Input: L>=11255, x>=1, root>=9L/16 and log(99x/40)<=L/600.
Claim: the contour, pole, principal and ramp errors satisfy the displayed caps.
Clear positive denominators and use the existing power-decay comparison.
Role: retain the finite-scale errors without introducing numerical certificates. -/
theorem gamma_four_fifths_leading_error_budgets {L x : ℝ} (hL : 11255 ≤ L) (hx : 1 ≤ x)
    (hroot : (9 / 16 : ℝ) * L ≤ Real.sqrt x) (hlog : Real.log (x * (99 / 40 : ℝ)) ≤ L / 600) :
    43 * x ^ (-9 / 16 : ℝ) ≤ 1 / 100 ∧
      ((7 / 6 : ℝ) * L + 4) / Real.sqrt x ≤ 21 / 10 ∧
      (Real.sqrt x / 8 + (1839 / 1000 : ℝ) * (2 * Real.log x + 3) + 21 / 10) / Real.sqrt x ≤
        3 / 20 ∧
      ((135 / 20 : ℝ) * Real.sqrt x +
            86 * ((1839 / 1000 : ℝ) * Real.log (x * (99 / 40)) + 21 / 20)) /
          Real.sqrt x ≤
        29 / 4 := by
  have hx0 := zero_lt_one.trans_le hx
  have hs := Real.sqrt_pos.mpr hx0
  have hlx : Real.log x ≤ Real.log (x * (99 / 40 : ℝ)) :=
    Real.log_le_log hx0 (by nlinarith only [hx])
  have hd :=
    PaperStatements.rpow_neg_nine_sixteenths_le_div_scale_sqrt (a := 1) (by norm_num only)
      (by
        norm_num only; exact hx)
  simp only [one_mul] at hd
  have hleft := mul_le_mul_of_nonneg_left hd (by norm_num only : (0 : ℝ) ≤ 43)
  have hleft' : 43 * (1 / Real.sqrt x) ≤ (1 / 100 : ℝ) := by
    rw [mul_one_div, div_le_iff₀ hs]
    linarith only [hroot, hL]
  refine ⟨hleft.trans hleft', ?_, ?_, ?_⟩
  · rw [div_le_iff₀ hs]
    linarith only [hroot, hL]
  · rw [div_le_iff₀ hs]
    linarith only [hlx, hlog, hroot, hL]
  · rw [div_le_iff₀ hs]
    linarith only [hlog, hroot, hL]

/-- Input: L>=11255. Claim: log((99/40)(32/99)L²)<=L/600.
Bound log(11255) by log(2^4*3^6), then use a logarithm tangent inequality.
Role: supply a continuous half-line profile without a new logarithm certificate. -/
theorem gamma_four_fifths_leading_cutoff_log {L : ℝ} (hL : 11255 ≤ L) :
    Real.log (((32 / 99 : ℝ) * L ^ 2) * (99 / 40)) ≤ L / 600 := by
  have hL0 : 0 < L := by linarith only [hL]
  have he : Real.log (11664 : ℝ) = 4 * Real.log 2 + 6 * Real.log 3 := by
    rw [show (11664 : ℝ) = 2 ^ 4 * 3 ^ 6 by norm_num only,
      Real.log_mul (by norm_num only : (2 : ℝ) ^ 4 ≠ 0) (by norm_num only : (3 : ℝ) ^ 6 ≠ 0),
      Real.log_pow, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
  have hm :=
    Real.log_le_log (by norm_num only : (0 : ℝ) < 11255) (by norm_num only : (11255 : ℝ) ≤ 11664)
  have ha : Real.log (11255 : ℝ) ≤ 937 / 100 := by
    linarith only [he, hm, Real.log_two_lt_d9, Real.log_three_lt_d9]
  have ht := Analysis.log_le_log_add_sub_div (by norm_num only : (0 : ℝ) < 11255) hL0
  have hl : Real.log L ≤ L / 1200 := by linarith only [ha, ht, hL]
  have hmul : ((32 / 99 : ℝ) * L ^ 2) * (99 / 40) ≤ L ^ 2 := by nlinarith only [sq_nonneg L]
  have hp : 0 < ((32 / 99 : ℝ) * L ^ 2) * (99 / 40) :=
    mul_pos (mul_pos (by norm_num only) (sq_pos_of_pos hL0)) (by norm_num only)
  have hlog := Real.log_le_log hp hmul
  rw [Real.log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  linarith only [hl, hlog]

end PseudoPrime.LLS
