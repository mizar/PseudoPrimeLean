/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.LogTaylorBounds
public import Mathlib.Analysis.Real.Pi.Bounds

/-! # Uniform logarithm enclosures for the middle-band checker -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

/-- The common Taylor range reduction is valid for every positive argument below 64. -/
private theorem log_cell_bounds {x : ℚ} (hx : 0 < x) (hu : x < 64) :
    (Analysis.rationalLogLower x 5 32 : ℝ) ≤ Real.log (x : ℝ) ∧
      Real.log (x : ℝ) ≤ (Analysis.rationalLogUpper x 5 32 : ℝ) := by
  apply Analysis.rationalLogBounds_sound hx
  apply abs_lt.mpr
  constructor <;> linarith only [hx, hu]

/-- The cell checker bounds both logarithms on the full middle band, with the lower
pi approximation in the right-endpoint argument. -/
theorem phaseCell_log_bounds {a b : ℚ} (ha : 35 / 2 ≤ a) (hab : a ≤ b) (hb : b ≤ 53 / 2) :
    let q := 2 * b / 7 - 2 / 3
    Real.log (a : ℝ) ≤ (Analysis.rationalLogUpper a 5 32 : ℝ) ∧
      (Analysis.rationalLogLower (6283 / 2000 * q) 5 32 : ℝ) ≤ Real.log (Real.pi * (q : ℝ)) := by
  let q := 2 * b / 7 - 2 / 3
  have hq : 0 < q := by
    dsimp only [q]; linarith only [ha, hab]
  have hm : 0 < 6283 / 2000 * q := mul_pos (by norm_num only) hq
  have ht : 6283 / 2000 * q < 64 := by
    dsimp only [q]; linarith only [hb]
  have hlog := (log_cell_bounds hm ht).1
  have hp : ((6283 / 2000 : ℚ) : ℝ) ≤ Real.pi := by
    norm_num only [Rat.cast_div, Rat.cast_ofNat]
    linarith only [Real.pi_gt_d4]
  have hle := mul_le_mul_of_nonneg_right hp ((Rat.cast_pos.mpr hq).le : 0 ≤ (q : ℝ))
  refine ⟨(log_cell_bounds (by linarith only [ha]) (by linarith only [hab, hb])).2, hlog.trans ?_⟩
  apply Real.log_le_log (Rat.cast_pos.mpr hm)
  simpa only [Rat.cast_mul] using hle

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
