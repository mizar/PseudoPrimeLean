/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaRefinedScale

/-! # Uniform geometry of the refined logarithmic tail profiles -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The real scale (32/99)(L+2 log L+c) squared for a variable
constant shift c. The tail bounds assume L at least 15000 and shifts
between ten and fifteen. Shift ten recovers the existing refined scale. -/
noncomputable def gammaTailProfileScale (L c : ℝ) : ℝ :=
  (32 / 99 : ℝ) * (L + 2 * Real.log L + c) ^ 2

/-- At shift ten the tail profile equals the existing refined
scale. Both definitions use the same real formula. This connects uniform
profile geometry to the already implemented arithmetic comparison. -/
theorem gamma_tail_profile_ten (L : ℝ) : gammaTailProfileScale L 10 = gammaRefinedScale L := by rfl

/-- For every L at least 15000, log L is at least nine. Compare
with log of two to the thirteenth power and use its certified lower bound. -/
theorem gamma_tail_log_lower {L : ℝ} (hL : 15000 ≤ L) : (9 : ℝ) ≤ Real.log L := by
  have he := Real.log_pow (2 : ℝ) 13
  norm_num only [Nat.cast_ofNat] at he
  have hm :=
    Real.log_le_log (by norm_num only : (0 : ℝ) < 8192)
      ((by norm_num only : (8192 : ℝ) ≤ 15000).trans hL)
  linarith only [hm, he, Real.log_two_gt_d9]

/-- For every L at least 15000, log L is at most (10/15000)L.
Bound log 15000 by ten, then use the logarithm tangent inequality at
the positive ratio L/15000. This gives a uniform logarithm-to-scale bound. -/
theorem gamma_tail_log_upper {L : ℝ} (hL : 15000 ≤ L) : Real.log L ≤ (10 / 15000 : ℝ) * L := by
  have hL0 : 0 < L := by linarith only [hL]
  have he := Real.log_pow (2 : ℝ) 14
  norm_num only [Nat.cast_ofNat] at he
  have hm :=
    Real.log_le_log (by norm_num only : (0 : ℝ) < 15000) (by norm_num only : (15000 : ℝ) ≤ 16384)
  have ha : Real.log (15000 : ℝ) ≤ 10 := by linarith only [he, hm, Real.log_two_lt_d9]
  have ht := Real.log_le_sub_one_of_pos (div_pos hL0 (by norm_num only : (0 : ℝ) < 15000))
  rw [Real.log_div hL0.ne' (by norm_num only : (15000 : ℝ) ≠ 0)] at ht
  linarith only [ht, ha, hL]

/-- For L at least 15000 and shift at least ten, the shifted root
is at least L plus 28. Combine the certified logarithm lower bound with
the shift assumption. The constant supplies the explicit tail main-term margin. -/
theorem gamma_tail_shift_lower {L c : ℝ} (hL : 15000 ≤ L) (hc : 10 ≤ c) :
    L + 28 ≤ L + 2 * Real.log L + c := by linarith only [gamma_tail_log_lower hL, hc]

/-- For L at least 15000 and shift at most fifteen, the shifted
root is at most (3007/3000)L. Use the uniform logarithm upper bound and
absorb the fixed shift into L. This controls all tail cutoff endpoints. -/
theorem gamma_tail_shift_upper {L c : ℝ} (hL : 15000 ≤ L) (hc : c ≤ 15) :
    L + 2 * Real.log L + c ≤ (3007 / 3000 : ℝ) * L := by
  linarith only [gamma_tail_log_upper hL, hc, hL]

/-- For L at least 15000 and shift at least ten, the tail scale
is at least (32/99)L squared. Compare the nonnegative shifted roots and
multiply their square inequality by the positive scale coefficient. -/
theorem gamma_tail_scale_lower {L c : ℝ} (hL : 15000 ≤ L) (hc : 10 ≤ c) :
    (32 / 99 : ℝ) * L ^ 2 ≤ gammaTailProfileScale L c := by
  have hL0 : 0 ≤ L := by linarith only [hL]
  have ht : L ≤ L + 2 * Real.log L + c := by linarith only [gamma_tail_shift_lower hL hc]
  have hs := (sq_le_sq₀ hL0 (hL0.trans ht)).mpr ht
  exact mul_le_mul_of_nonneg_left hs (by norm_num only : (0 : ℝ) ≤ 32 / 99)

/-- For every tail profile with L at least 15000 and shift at
least ten, its scale is at least three to the sixteenth power. Square
the logarithmic threshold and apply the preceding scale lower bound. -/
theorem gamma_tail_scale_large {L c : ℝ} (hL : 15000 ≤ L) (hc : 10 ≤ c) :
    (3 : ℝ) ^ 16 ≤ gammaTailProfileScale L c := by
  have hl := gamma_tail_scale_lower hL hc
  have hs := (sq_le_sq₀ (by norm_num only : (0 : ℝ) ≤ 15000) (by linarith only [hL] : 0 ≤ L)).mpr hL
  norm_num only
  nlinarith only [hl, hs]

/-- The square root of every tail scale is at least (9/16)L.
Assume L at least 15000 and shift at least ten. Certify the rational
squared-root coefficient using the scale lower bound and square nonnegativity. -/
theorem gamma_tail_scale_sqrt_lower {L c : ℝ} (hL : 15000 ≤ L) (hc : 10 ≤ c) :
    (9 / 16 : ℝ) * L ≤ Real.sqrt (gammaTailProfileScale L c) := by
  have hl := gamma_tail_scale_lower hL hc
  have hx0 : 0 ≤ gammaTailProfileScale L c :=
    (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 32 / 99) (sq_nonneg L)).trans hl
  apply (Real.le_sqrt (by linarith only [hL] : (0 : ℝ) ≤ 9 / 16 * L) hx0).mpr
  nlinarith only [hl, sq_nonneg L]

/-- For L at least 15000 and shift between ten and fifteen, the
actual cutoff (99/40)x is strictly below L squared. Square the uniform
shift upper bound and verify the strict rational coefficient inequality. -/
theorem gamma_tail_cutoff_lt_square {L c : ℝ} (hL : 15000 ≤ L) (hc : 10 ≤ c) (hcu : c ≤ 15) :
    (99 / 40 : ℝ) * gammaTailProfileScale L c < L ^ 2 := by
  have hL0 : 0 < L := by linarith only [hL]
  have ht0 : 0 ≤ L + 2 * Real.log L + c := by linarith only [gamma_tail_shift_lower hL hc, hL]
  have ht := gamma_tail_shift_upper hL hcu
  have hs := (sq_le_sq₀ ht0 (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 3007 / 3000) hL0.le)).mpr ht
  dsimp only [gammaTailProfileScale]
  nlinarith only [hs, sq_pos_of_pos hL0]

/-- For every tail profile in the stated L and shift range,
the logarithm of its actual cutoff is at most (20/15000)L. Use the strict
cutoff-to-square comparison and the uniform logarithm upper bound. -/
theorem gamma_tail_cutoff_log_upper {L c : ℝ} (hL : 15000 ≤ L) (hc : 10 ≤ c) (hcu : c ≤ 15) :
    Real.log ((99 / 40 : ℝ) * gammaTailProfileScale L c) ≤ (20 / 15000 : ℝ) * L := by
  have hx0 : 0 < (99 / 40 : ℝ) * gammaTailProfileScale L c :=
    mul_pos (by norm_num only)
      ((by norm_num only : (0 : ℝ) < 3 ^ 16).trans_le (gamma_tail_scale_large hL hc))
  have hl := Real.log_le_log hx0 (gamma_tail_cutoff_lt_square hL hc hcu).le
  rw [Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  linarith only [hl, gamma_tail_log_upper hL]

/-- For every tail profile with L at least 15000 and shift between ten
and fifteen, the cutoff logarithm is at most twice log L. This retains
the logarithmic denominator needed by the prime-factor count estimate.
Compare the positive cutoff with L squared and apply log monotonicity. -/
theorem gamma_tail_cutoff_log_le_twice_log {L c : ℝ} (hL : 15000 ≤ L) (hc : 10 ≤ c) (hcu : c ≤ 15) :
    Real.log ((99 / 40 : ℝ) * gammaTailProfileScale L c) ≤ 2 * Real.log L := by
  have hx0 : 0 < (99 / 40 : ℝ) * gammaTailProfileScale L c :=
    mul_pos (by norm_num only)
      ((by norm_num only : (0 : ℝ) < 3 ^ 16).trans_le (gamma_tail_scale_large hL hc))
  have hl := Real.log_le_log hx0 (gamma_tail_cutoff_lt_square hL hc hcu).le
  rw [Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  exact hl

end PseudoPrime.Analysis
