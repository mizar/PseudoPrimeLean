/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.SquareFactorLogBounds

/-! # Logarithmic certificates for square-divisor stages -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The rational logarithm certificate supplies stage 0's lower bound. -/
theorem square_factor_stage_log0 : (21 : ℝ) ≤ Real.log (2087485597 : ℝ) := by
  have h :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 2087485597 31 32 21 23 = true from by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat] at h
  exact h

/-- The rational logarithm certificate supplies stage 1's lower bound. -/
theorem square_factor_stage_log1 : (27 : ℝ) ≤ Real.log (1488482619461 : ℝ) := by
  have h :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 1488482619461 41 32 27 30 = true from by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat] at h
  exact h

/-- The rational logarithm certificate supplies stage 2's lower bound. -/
theorem square_factor_stage_log2 : (31 : ℝ) ≤ Real.log (68854718408874 : ℝ) := by
  have h :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 68854718408874 46 32 31 33 = true from by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat] at h
  exact h

/-- The rational logarithm certificate supplies stage 3's lower bound. -/
theorem square_factor_stage_log3 : (37 : ℝ) ≤ Real.log (14459490865863331 : ℝ) := by
  have h :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 14459490865863331 54 32 37 39 = true from by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat] at h
  exact h

/-- The rational logarithm certificate supplies stage 4's lower bound. -/
theorem square_factor_stage_log4 : (41 : ℝ) ≤ Real.log (1525476286348581316 : ℝ) := by
  have h :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 1525476286348581316 61 32 41 43 = true from by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat] at h
  exact h

/-- The rational logarithm certificate supplies stage 5's lower bound. -/
theorem square_factor_stage_log5 : (46 : ℝ) ≤ Real.log (107800324235299746261 : ℝ) := by
  have h :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 107800324235299746261 67 32 46 48 = true from by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat] at h
  exact h

/-- The rational logarithm certificate supplies stage 6's lower bound. -/
theorem square_factor_stage_log6 : (50 : ℝ) ≤ Real.log (5740367265529711488345 : ℝ) := by
  have h :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 5740367265529711488345 73 32 50 52 = true from by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat] at h
  exact h

end PseudoPrime.PrimeTestBounds.MillerRabin
