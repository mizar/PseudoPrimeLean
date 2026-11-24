/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaCellArithmetic
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaCellLogBounds

/-! # Real inequality certified by a middle-band cell -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem phase_main_nonneg {b : ℝ} (hl : 35 / 2 ≤ b) (hr : b ≤ 53 / 2) :
    0 ≤ b / 2 - Real.log (Real.pi * (2 * b / 7 - 2 / 3)) := by
  have hq : 0 < 2 * b / 7 - 2 / 3 := by linarith only [hl]
  have hm := mul_le_mul_of_nonneg_right Real.pi_lt_four.le hq.le
  have ht : Real.pi * (2 * b / 7 - 2 / 3) ≤ 2 ^ 5 := by linarith only [hm, hr]
  have hlog := Real.log_le_log (mul_pos Real.pi_pos hq) ht
  rw [Real.log_pow] at hlog
  linarith only [hlog, Real.log_le_sub_one_of_pos (by norm_num only : (0 : ℝ) < 2), hl]

/-- Nonnegative computed slack implies the real Lee–Nosal cell inequality with the
actual logarithms and pi. Endpoint phase caps are supplied by the separate node certificate. -/
theorem phaseCellSlack_sound {a b u v : ℚ} (ha : 35 / 2 ≤ a) (hab : a ≤ b) (hb : b ≤ 53 / 2)
    (hs : 0 ≤ phaseCellSlack a b u v) :
    let q := 2 * (b : ℝ) / 7 - 2 / 3
    let A := (b : ℝ) / 2 - Real.log (Real.pi * q)
    q / 2 + (max 0 (max (u : ℝ) (v : ℝ)) + 3611 * ((b : ℝ) - a + 1 / 2800) ^ 2 / 8) +
          (A ^ 2 + 3 / 2 * A + 3 / 2) / (2 * Real.pi) -
        579 / 5000 ≤
      (a : ℝ) * (a - Real.log a) / (8 * Real.pi) := by
  let q := 2 * b / 7 - 2 / 3
  let A := (b : ℝ) / 2 - Real.log (Real.pi * (q : ℝ))
  let B := (b : ℝ) / 2 - (Analysis.rationalLogLower (6283 / 2000 * q) 5 32 : ℝ)
  have hal : (35 / 2 : ℝ) ≤ a := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr ha
  have hbr : (b : ℝ) ≤ 53 / 2 := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr hb
  have hbl := hal.trans ((Rat.cast_le (K := ℝ)).mpr hab)
  have hqc : (q : ℝ) = 2 * (b : ℝ) / 7 - 2 / 3 := by
    simp only [q, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat]
  have hz : 0 ≤ A := by simpa only [A, hqc] using phase_main_nonneg hbl hbr
  have hlog := phaseCell_log_bounds ha hab hb
  have hAB : A ≤ B := sub_le_sub_left hlog.2 _
  have hnum := pow_le_pow_left₀ hz hAB 2
  have hpL : (6283 / 2000 : ℝ) ≤ Real.pi := by linarith only [Real.pi_gt_d4]
  have hpU : Real.pi ≤ (3927 / 1250 : ℝ) := by linarith only [Real.pi_lt_d4]
  have hm :=
    div_le_div₀ (by linarith only [hz.trans hAB, sq_nonneg B] : 0 ≤ B ^ 2 + 3 / 2 * B + 3 / 2)
      (by linarith only [hAB, hnum] : A ^ 2 + 3 / 2 * A + 3 / 2 ≤ B ^ 2 + 3 / 2 * B + 3 / 2)
      (by norm_num only : (0 : ℝ) < 2 * (6283 / 2000))
      (mul_le_mul_of_nonneg_left hpL (by norm_num only : (0 : ℝ) ≤ 2))
  have ha0 : 0 < (a : ℝ) := by linarith only [hal]
  have htar := mul_le_mul_of_nonneg_left (sub_le_sub_left hlog.1 (a : ℝ)) ha0.le
  have ht1 := div_le_div_of_nonneg_right htar (by norm_num only : (0 : ℝ) ≤ 8 * (3927 / 1250))
  have ht2 :=
    div_le_div_of_nonneg_left
      (mul_nonneg ha0.le
        (by linarith only [Real.log_le_sub_one_of_pos ha0] : 0 ≤ (a : ℝ) - Real.log a))
      (mul_pos (by norm_num only : (0 : ℝ) < 8) Real.pi_pos)
      (mul_le_mul_of_nonneg_left hpU (by norm_num only : (0 : ℝ) ≤ 8))
  have hs' := (Rat.cast_nonneg (K := ℝ)).mpr hs
  simp only [phaseCellSlack, Rat.cast_sub, Rat.cast_div, Rat.cast_mul, Rat.cast_pow, Rat.cast_max,
    Rat.cast_add, Rat.cast_zero, Rat.cast_ofNat] at hs'
  dsimp only
  dsimp only [A, B] at hm
  rw [hqc] at hm
  linarith only [hs', hm, ht1.trans ht2]

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
