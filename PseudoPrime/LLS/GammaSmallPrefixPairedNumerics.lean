/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaEvenPairedNumerics

/-! # Paired analytic error budgets with a small Euler prefix -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Input: L >= 215. Claim: log(L) <= (1/40)L on the whole half-line.
Use a rational logarithm certificate at 215 and the tangent inequality.
Role: control smoothed arithmetic errors without finite interval tables. -/
theorem small_prefix_nearSquare_log_bound {L : ℝ} (hL : 215 ≤ L) :
    Real.log L ≤ (1 / 40 : ℝ) * L := by
  have hc : Analysis.rationalLogIntervalCheck 215 8 16 5 (43 / 8) = true := by decide +kernel
  have ha := (Analysis.rationalLogIntervalCheck_sound hc).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at ha
  have hL0 : 0 < L := by linarith only [hL]
  have ht := Analysis.log_le_log_add_sub_div (by norm_num only : (0 : ℝ) < 215) hL0
  nlinarith only [ha, ht, hL]

/-- Input: L >= 215. Claim: log((101/40)(2/5)L^2) <= (269/5375)L.
Factor the argument and use the half-line logarithm bound.
Role: control the enlarged endpoint of the paired-jump error. -/
theorem small_prefix_nearSquare_extended_log_bound {L : ℝ} (hL : 215 ≤ L) :
    Real.log ((101 / 40 : ℝ) * ((2 / 5 : ℝ) * L ^ 2)) ≤ (269 / 5375 : ℝ) * L := by
  have hL0 : 0 < L := by linarith only [hL]
  have he : (101 / 40 : ℝ) * ((2 / 5 : ℝ) * L ^ 2) = (101 / 100 : ℝ) * L ^ 2 := by ring
  rw [he, Real.log_mul (by norm_num only) (sq_pos_of_pos hL0).ne', Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  have hr := Real.log_le_sub_one_of_pos (by norm_num only : (0 : ℝ) < 101 / 100)
  linarith only [hr, small_prefix_nearSquare_log_bound hL, hL]

/-- Input: L >= 215 and x=(2/5)L^2. Claim: the paired ramp error, principal
error and main gap satisfy the displayed uniform budgets. Retain log(2/5) <= -9/10
and use the certified ramp mass. Role: combine an analytic Euler prefix lower
bound with the reduced MR entrance on the whole half-line. -/
theorem gamma_small_prefix_nearSquare_budgets {L : ℝ} (hL : 215 ≤ L) :
    let x := (2 / 5 : ℝ) * L ^ 2;
    gammaRampPairedErrorNumerator x / Real.sqrt x ≤ Real.sqrt x / 200 + 49 / 20 ∧
      (Real.sqrt x / 20 + (5517 / 4000 : ℝ) * Real.log x + 2469 / 800) / Real.sqrt x ≤ 1 / 5 ∧
      ((11783423 / 25000000 : ℝ) + 19 / 400) * L <
        (2 * (∫ u in (0 : ℝ)..(99 / 40), Analysis.exponentialRampWeight u) - 1 - 1 / 100) *
          Real.sqrt x := by
  dsimp only
  let x := (2 / 5 : ℝ) * L ^ 2
  have hL0 : 0 < L := by linarith only [hL]
  have hx : 1 ≤ x := by
    dsimp only [x]
    nlinarith only [hL, sq_nonneg (L - 215)]
  have hx0 := zero_lt_one.trans_le hx
  have hs := Real.sqrt_pos.mpr hx0
  have hroot : (79 / 125 : ℝ) * L ≤ Real.sqrt x := by
    apply (Real.le_sqrt (mul_nonneg (by norm_num only) hL0.le) hx0.le).mpr
    dsimp only [x]
    nlinarith only [sq_nonneg L]
  have hlogext := small_prefix_nearSquare_extended_log_bound hL
  change Real.log ((101 / 40 : ℝ) * x) ≤ (269 / 5375 : ℝ) * L at hlogext
  have hlogx : Real.log x ≤ (1 / 20 : ℝ) * L - 9 / 10 := by
    have hcheck : Analysis.rationalLogIntervalCheck (5 / 2) 2 16 (9 / 10) 1 = true := by
      decide +kernel
    have hc := (Analysis.rationalLogIntervalCheck_sound hcheck).1
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at hc
    have hi : Real.log (2 / 5 : ℝ) ≤ -9 / 10 := by
      rw [show (2 / 5 : ℝ) = (5 / 2)⁻¹ by norm_num only, Real.log_inv]
      linarith only [hc]
    dsimp only [x]
    rw [Real.log_mul (by norm_num only : (2 / 5 : ℝ) ≠ 0) (sq_pos_of_pos hL0).ne', Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [hi, small_prefix_nearSquare_log_bound hL]
  have hlogr :=
    (Real.log_le_log (mul_pos hx0 (by norm_num only : (0 : ℝ) < 99 / 40))
          (show x * (99 / 40) ≤ (101 / 40 : ℝ) * x by linarith only [hx])).trans
      hlogext
  refine ⟨?_, ?_, ?_⟩
  · rw [div_le_iff₀ hs]
    unfold gammaRampPairedErrorNumerator rampSmoothedIncrementError rampExtendedSmoothedError
    have hsq := Real.sq_sqrt hx0.le
    nlinarith only [hlogext, hlogr, hroot, hL, hx, hsq]
  · rw [div_le_iff₀ hs]
    linarith only [hlogx, hroot, hL]
  · have hm := mul_le_mul_of_nonneg_right Analysis.gamma_ramp_mass_lower (Real.sqrt_nonneg x)
    nlinarith only [hm, hroot, hL]

end PseudoPrime.LLS
