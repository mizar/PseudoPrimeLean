/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PrimitiveLogMainErrorBounds
public import PseudoPrime.Analysis.SharperPart2CutoffBounds
public import PseudoPrime.Analysis.EulerMascheroniBounds
public import PseudoPrime.Analysis.LogTaylorBounds

/-! # Main-error regime below the old cutoff 64 -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- At x at least 59 the odd logarithmic main error is at most -11/4.
Use the certified logarithm of 59 and the existing Euler-constant lower bound.
This supplies the odd logarithmic input below the old cutoff 64. -/
theorem primitiveLogOddMainError_le_fixed_of_ge59 {x : ℝ} (hx : 59 ≤ x) :
    primitiveLogOddMainError x ≤ -(11 / 4 : ℝ) := by
  have hc : rationalLogIntervalCheck 59 6 10 (407 / 100) (408 / 100) = true := by decide +kernel
  have hl := (rationalLogIntervalCheck_sound hc).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl
  have hm := Real.log_le_log (by norm_num only : (0 : ℝ) < 59) hx
  have hlog : (407 / 100 : ℝ) ≤ Real.log x := hl.trans hm
  have hcoef : (1961 / 2000 : ℝ) ≤ Real.log 2 + Real.eulerMascheroniConstant / 2 := by
    linarith only [Real.log_two_gt_d9, twentyThree_fortieths_lt_eulerMascheroniConstant]
  have hp :=
    mul_le_mul hcoef hlog (by norm_num only : (0 : ℝ) ≤ 407 / 100)
      (le_trans (by norm_num only) hcoef)
  unfold primitiveLogOddMainError
  nlinarith only [hp, Real.pi_lt_d4, Real.pi_pos]

/-- At x at least 59 the even logarithmic main error is at most -11/4.
The logarithm exceeds four, so the negative quadratic term gives ample margin.
This supplies the even branch of the parameterized logarithmic estimate. -/
theorem primitiveLogEvenMainError_le_fixed_of_ge59 {x : ℝ} (hx : 59 ≤ x) :
    primitiveLogEvenMainError x ≤ -(11 / 4 : ℝ) := by
  have hl := Real.log_le_log (by norm_num only : (0 : ℝ) < 59) hx
  have hlog59 : (4 : ℝ) ≤ Real.log 59 := by
    have h : rationalLogIntervalCheck 59 6 10 4 (408 / 100) = true := by decide +kernel
    have ht := (rationalLogIntervalCheck_sound h).1
    norm_num only [Rat.cast_ofNat] at ht
    exact ht
  have hlog : (4 : ℝ) ≤ Real.log x := hlog59.trans hl
  have hprod :=
    mul_le_mul_of_nonneg_right Real.one_half_lt_eulerMascheroniConstant.le
      (le_trans (by norm_num only) hlog)
  unfold primitiveLogEvenMainError
  nlinarith only [hprod, hlog, Real.pi_lt_four, Real.pi_pos]

/-- At x at least 59 the odd reciprocal main error is at most -1/4.
Retain the factor 1-1/x and use the Euler-constant lower bound 23/40.
This supplies the odd branch of the reciprocal zero-mass estimate. -/
theorem primitiveReciprocalOddMainError_le_fixed_of_ge59 {x : ℝ} (hx : 59 ≤ x) :
    primitiveReciprocalOddMainError x ≤ -(1 / 4 : ℝ) := by
  have hxp : 0 < x := by linarith only [hx]
  have hi : 1 / x ≤ (1 / 59 : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num only) (by norm_num only) hx
  have hc : 0 ≤ 1 - 1 / x := by linarith only [hi]
  have hg := mul_le_mul_of_nonneg_right twentyThree_fortieths_lt_eulerMascheroniConstant.le hc
  have hl := mul_le_mul_of_nonneg_right Real.log_two_lt_d9.le (inv_nonneg.mpr hxp.le)
  unfold primitiveReciprocalOddMainError
  simp only [div_eq_mul_inv] at hi hg ⊢
  nlinarith only [hg, hl, hi]

/-- At x at least 59 the even reciprocal main error is at most -1/4.
Monotonicity of the logarithmic ratio controls the positive tail term.
This supplies the even branch without changing the reciprocal constant. -/
theorem primitiveReciprocalEvenMainError_le_fixed_of_ge59 {x : ℝ} (hx : 59 ≤ x) :
    primitiveReciprocalEvenMainError x ≤ -(1 / 4 : ℝ) := by
  have hxp : 0 < x := by linarith only [hx]
  have hi : 1 / x ≤ (1 / 59 : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num only) (by norm_num only) hx
  have hc : 0 ≤ 1 - 1 / x := by linarith only [hi]
  have hg := mul_le_mul_of_nonneg_right Real.one_half_lt_eulerMascheroniConstant.le hc
  have hlog : 0 ≤ Real.log x := Real.log_nonneg (by linarith only [hx])
  have hr : (Real.log x + 1) / x ≤ logLinearRatio x := by
    unfold logLinearRatio
    exact div_le_div_of_nonneg_right (by linarith only [hlog]) hxp.le
  have hm :=
    strictAntiOn_logLinearRatio.antitoneOn (by norm_num only [Set.mem_Ici])
      (by
        simp only [Set.mem_Ici]; linarith only [hx])
      hx
  have hb : Real.log (59 : ℝ) ≤ (408 / 100 : ℝ) := by
    have ht : rationalLogIntervalCheck 59 6 10 4 (408 / 100) = true := by decide +kernel
    have h := (rationalLogIntervalCheck_sound ht).2
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    linarith only [h]
  unfold logLinearRatio at hr hm
  unfold primitiveReciprocalEvenMainError
  simp only [div_eq_mul_inv] at hr hm hg ⊢
  nlinarith only [hr, hm, hb, hg, Real.log_two_gt_d9]

/-- For t at least six, log t is at most t/3.
The logarithm tangent at eight gives the inequality on the entire half-line.
This controls quadratic logarithmic terms below root height eight. -/
theorem log_le_third_of_ge_six {t : ℝ} (ht : 6 ≤ t) : Real.log t ≤ t / 3 := by
  have ht0 : 0 < t := by linarith only [ht]
  have hl := log_le_log_add_sub_div (a := (8 : ℝ)) (y := t) (by norm_num only) ht0
  have h8 : Real.log (8 : ℝ) ≤ (21 / 10 : ℝ) := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num only, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [Real.log_two_lt_d9]
  linarith only [hl, h8, ht]

/-- Every level q at least 1053 has log q at least 695939/100000.
A short rational Taylor certificate and monotonicity give the whole half-line.
This is an analytic entrance, with no enumeration of moduli. -/
theorem log_level_ge_below64_entrance {q : ℕ} (hq : 1053 ≤ q) :
    (695939 / 100000 : ℝ) ≤ Real.log q := by
  have hc : rationalLogIntervalCheck 1053 10 10 (695939 / 100000) (174 / 25) = true := by
    decide +kernel
  have hl := (rationalLogIntervalCheck_sound hc).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl
  exact hl.trans (Real.log_le_log (by norm_num only) (by exact_mod_cast hq))

/-- Above the rational logarithmic entrance, the precise Part 2 root
exceeds 15/2 and its square is at least 59. Certify the endpoint logarithm
and use its tangent to control all larger inputs. Both conditions needed
by the lower-cutoff comparison follow from this single root estimate. -/
theorem sharperPart2Root_height_and_cutoff {L : ℝ} (hL : (695939 / 100000 : ℝ) ≤ L) :
    (15 / 2 : ℝ) < sharperPart2CutoffRoot L ∧ 59 ≤ (sharperPart2CutoffRoot L) ^ 2 := by
  have hL0 : 0 < L := by linarith only [hL]
  have hc :
    rationalLogIntervalCheck (695939 / 100000) 3 12 (194 / 100) (1940093 / 1000000) = true := by
    decide +kernel
  have hl := (rationalLogIntervalCheck_sound hc).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl
  have ht := log_le_log_add_sub_div (a := (695939 / 100000 : ℝ)) (y := L) (by norm_num only) hL0
  have hb : (19203 / 2500 : ℝ) ≤ sharperPart2CutoffRoot L := by
    unfold sharperPart2CutoffRoot
    linarith only [ht, hl, hL]
  constructor
  · linarith only [hb]
  · nlinarith only [hb]

end PseudoPrime.Analysis
