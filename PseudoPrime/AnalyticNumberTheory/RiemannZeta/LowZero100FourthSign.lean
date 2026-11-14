/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100NormalizedApprox
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100RotatedBounds
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100PhaseChecks.Node004Finite
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100PhaseChecks.Node004Log
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100PhaseChecks.Node004PreciseLog

/-! # The fourth low-zero lower endpoint -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- At the fourth lower endpoint `31155 / 1024`, the real critical-line xi value is negative.
An internally checked rational finite approximation and analytic error bounds prove the sign
without assuming RH or importing an external table of zero locations. -/
theorem low_zero_fourth_lower_sign :
    (RiemannXi.riemannXi (((1 / 2 : ℝ) : ℂ) + (((31155 / 1024 : ℝ) : ℂ) * Complex.I))).re < 0 := by
  have hcalc : (9311 / 100000000 : ℝ) ≤ ((endpointRotatedFinite (31155 / 1024)).1 : ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr endpoint004_finite_lower
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
    exact h
  have herr :=
    abs_le.mp
      (abs_endpoint_rotated_error (31155 / 1024) (by norm_num only) (by norm_num only)
        endpoint004_log_check endpoint004_precise_log_check)
  apply xi_neg_of_finite_em8 (by norm_num only) (by norm_num only)
  linarith only [hcalc, herr.1]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
