/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaRefinedScale

/-! # Cutoff coverage for the fixed finite Euler certificates -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Throughout the prescribed logarithmic range, the refined witness
cutoff covers 50000. The shift is at least 250; square the nonnegative
comparison and use the exact scale-to-cutoff identity. This discharges
the finite prefix inclusion condition in the refined arithmetic comparison. -/
theorem gamma_refined_cutoff_ge_fifty_thousand {L : ℝ} (hL : 100 * Real.log 10 ≤ L) :
    (50000 : ℝ) ≤ (99 / 40 : ℝ) * gammaRefinedScale L := by
  have hT : (250 : ℝ) ≤ L + 2 * Real.log L + 10 := by
    linarith only [gamma_refined_log_lower hL, gamma_refined_log_log_lower hL]
  have hs :=
    (sq_le_sq₀ (by norm_num only : (0 : ℝ) ≤ 250)
          (by linarith only [hT] : 0 ≤ L + 2 * Real.log L + 10)).mpr
      hT
  rw [gamma_refined_scale_cutoff]
  nlinarith only [hs]

/-- Every natural input at least ten to the hundredth power has a
refined cutoff covering 50000. Apply the decimal logarithmic range
and the proved real-cutoff lower bound. -/
theorem gamma_refined_integer_cutoff_ge_fifty_thousand {n : ℕ} (hn : 10 ^ 100 ≤ n) :
    (50000 : ℝ) ≤ (99 / 40 : ℝ) * gammaRefinedScale (Real.log n) := by
  exact gamma_refined_cutoff_ge_fifty_thousand (gamma_refined_log_range_of_decimal hn)

end PseudoPrime.Analysis
