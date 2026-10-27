/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaSmoothedPrincipalBounds
public import PseudoPrime.Analysis.LogTaylorBounds

/-! # Whole-half-line budgets for the paired near-square ramp comparison -/

@[expose] public section

namespace PseudoPrime.LLS

/-- For every L at least 550, log L is at most (23/2000)L.
A short rational logarithm certificate at 550 and the logarithm tangent
give the bound on the whole half-line. This controls the enlarged ramp. -/
theorem principal_paired_nearSquare_log_bound {L : ℝ} (hL : 550 ≤ L) :
    Real.log L ≤ (23 / 2000 : ℝ) * L := by
  have hc : Analysis.rationalLogIntervalCheck 550 9 12 6 (631 / 100) = true := by decide +kernel
  have ha := (Analysis.rationalLogIntervalCheck_sound hc).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at ha
  have hL0 : 0 < L := by linarith only [hL]
  have ht := Analysis.log_le_log_add_sub_div (by norm_num only : (0 : ℝ) < 550) hL0
  nlinarith only [ha, ht, hL]

/-- For L at least 550 and x=(2/5)L squared, log((101/40)x) is at most
(231/10000)L. Factor the argument as (101/100)L squared and use the
whole-half-line logarithm bound. This covers the Chebyshev stencil endpoint. -/
theorem principal_paired_nearSquare_extended_log_bound {L : ℝ} (hL : 550 ≤ L) :
    Real.log ((101 / 40 : ℝ) * ((2 / 5 : ℝ) * L ^ 2)) ≤ (231 / 10000 : ℝ) * L := by
  have hL0 : 0 < L := by linarith only [hL]
  have he : (101 / 40 : ℝ) * ((2 / 5 : ℝ) * L ^ 2) = (101 / 100 : ℝ) * L ^ 2 := by ring
  rw [he, Real.log_mul (by norm_num only) (sq_pos_of_pos hL0).ne', Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  have hr := Real.log_le_sub_one_of_pos (by norm_num only : (0 : ℝ) < 101 / 100)
  linarith only [hr, principal_paired_nearSquare_log_bound hL, hL]

/-- At L at least 550 and x=(2/5)L squared, the paired ramp error is at most
sqrt(x)/200+2, the principal error at most 3/10, and the ramp main term
after its linear loss exceeds (M+9/200)L.
Use the enlarged logarithmic endpoint and certified ramp mass on the whole
half-line. These budgets close a uniform negative-witness comparison. -/
theorem gamma_principal_paired_nearSquare_budgets {L : ℝ} (hL : 550 ≤ L) :
    let x := (2 / 5 : ℝ) * L ^ 2;
    gammaRampPairedErrorNumerator x / Real.sqrt x ≤ Real.sqrt x / 200 + 2 ∧
      (Real.sqrt x / 8 + (1839 / 1000 : ℝ) * (2 * Real.log x + 3) + 21 / 10) / Real.sqrt x ≤
        3 / 10 ∧
      ((11783423 / 25000000 : ℝ) + 9 / 200) * L <
        (2 * (∫ u in (0 : ℝ)..(99 / 40), Analysis.exponentialRampWeight u) - 1 - 1 / 100) *
          Real.sqrt x := by
  dsimp only
  let x := (2 / 5 : ℝ) * L ^ 2
  have hL0 : 0 < L := by linarith only [hL]
  have hx : 1 ≤ x := by
    dsimp only [x]
    nlinarith only [hL, sq_nonneg (L - 550)]
  have hx0 := zero_lt_one.trans_le hx
  have hs := Real.sqrt_pos.mpr hx0
  have hroot : (63 / 100 : ℝ) * L ≤ Real.sqrt x := by
    apply (Real.le_sqrt (mul_nonneg (by norm_num only) hL0.le) hx0.le).mpr
    dsimp only [x]
    nlinarith only [sq_nonneg L]
  have hlogext := principal_paired_nearSquare_extended_log_bound hL
  change Real.log ((101 / 40 : ℝ) * x) ≤ (231 / 10000 : ℝ) * L at hlogext
  have hlogx :=
    (Real.log_le_log hx0 (show x ≤ (101 / 40 : ℝ) * x by linarith only [hx])).trans hlogext
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
