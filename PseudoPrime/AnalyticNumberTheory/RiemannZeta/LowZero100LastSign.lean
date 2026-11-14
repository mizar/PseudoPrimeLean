/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100NormalizedApprox
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100RotatedBounds
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100PhaseChecks.Node029Finite
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100PhaseChecks.Node029Log

/-! # The last low-zero lower endpoint -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- At the twenty-ninth lower endpoint `101203 / 1024`, the real critical-line xi value is
positive. An internally checked rational finite approximation and analytic error bounds prove
the sign without assuming RH or importing an external table of zero locations. -/
theorem low_zero_last_lower_sign :
    0 < (RiemannXi.riemannXi (((1 / 2 : ℝ) : ℂ) + (((101203 / 1024 : ℝ) : ℂ) * Complex.I))).re := by
  have hcalc : ((endpointRotatedFinite (101203 / 1024)).1 : ℝ) < (-49036 / 100000000 : ℝ) := by
    have h := (Rat.cast_lt (K := ℝ)).mpr endpoint029_finite_upper
    norm_num only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] at h
    norm_num only
    exact h
  have herr :=
    abs_le.mp
      (abs_endpoint_rotated_common (101203 / 1024) (by norm_num only) (by norm_num only)
        endpoint029_log_check)
  apply xi_pos_of_finite_em8 (by norm_num only) (by norm_num only)
  linarith only [hcalc, herr.2]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
