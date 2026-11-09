/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.RealLog
public import PseudoPrime.Analysis.PreciseLogTaylorBounds

/-! # Exponential factor comparison on the low logarithmic range -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For `8 ≤ L ≤ 25/2`, the bound `exp (L/3)` is at most `(517/1250) * L²`.
A logarithm tangent compares the normalized exponential with its right endpoint, whose
rational upper bound is certified by a Taylor interval for `log (323/5)`. -/
theorem exp_factor_le_4136 {L : ℝ} (hlo : 8 ≤ L) (hhi : L ≤ 25 / 2) :
    Real.exp (L / 3) ≤ (517 / 1250 : ℝ) * L ^ 2 := by
  have hL : 0 < L := by linarith only [hlo]
  have hT : (0 : ℝ) < 25 / 2 := by norm_num only
  have hdelta : (0 : ℝ) ≤ 25 / 2 - L := by linarith only [hhi]
  have ht := Analysis.log_le_log_add_sub_div (a := L) (y := (25 / 2 : ℝ)) hL hT
  have hd :=
    div_le_div_of_nonneg_left hdelta (by norm_num only : (0 : ℝ) < 6)
      (by linarith only [hlo] : (6 : ℝ) ≤ L)
  have hc : L / 3 - 2 * Real.log L ≤ (25 / 2 : ℝ) / 3 - 2 * Real.log (25 / 2) := by
    linarith only [ht, hd]
  have he := Real.exp_le_exp.mpr hc
  have hEL : Real.exp (2 * Real.log L) = L ^ 2 := by
    simpa only [Nat.cast_ofNat, Real.exp_log hL] using (Real.exp_nat_mul (Real.log L) 2)
  have hET : Real.exp (2 * Real.log (25 / 2)) = (25 / 2 : ℝ) ^ 2 := by
    simpa only [Nat.cast_ofNat, Real.exp_log hT] using (Real.exp_nat_mul (Real.log (25 / 2)) 2)
  rw [Real.exp_sub, Real.exp_sub, hEL, hET] at he
  have hlog : (25 / 6 : ℝ) ≤ Real.log (323 / 5) := by
    have hc : Analysis.preciseLogCheck (323 / 5) 7 64 (25 / 6) 5 = true := by decide +kernel
    have h := (Analysis.preciseLogCheck_sound hc).1
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
    exact h
  have hExp : Real.exp (25 / 6 : ℝ) ≤ 323 / 5 := by
    have h := Real.exp_le_exp.mpr hlog
    rw [Real.exp_log (by norm_num only : (0 : ℝ) < 323 / 5)] at h
    exact h
  have hratio : Real.exp (L / 3) / L ^ 2 ≤ (323 / 5 : ℝ) / (25 / 2) ^ 2 := by
    apply he.trans
    have heq : ((25 / 2 : ℝ) / 3) = 25 / 6 := by norm_num only
    rw [heq]
    exact div_le_div_of_nonneg_right hExp (sq_nonneg _)
  have hp := (div_le_iff₀ (sq_pos_of_pos hL)).mp hratio
  nlinarith only [hp, sq_nonneg L]

end PseudoPrime.PrimeTestBounds.MillerRabin
