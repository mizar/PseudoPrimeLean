/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.LogTaylorBounds

/-! # Logarithm endpoint for the Euler total -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

-- Exact rational reduction checks this logarithm endpoint independently.
/-- The rational logarithm certificate bounds the large Euler cutoff by 28. -/
theorem quarter_euler_total_log_check :
    Analysis.rationalLogIntervalCheck 1000000000000 40 32 0 28 = true := by decide +kernel

/-- The logarithm of the large Euler cutoff is at most 28. -/
theorem quarter_euler_total_log : Real.log (1000000000000 : ℝ) ≤ 28 := by
  have h := (Analysis.rationalLogIntervalCheck_sound quarter_euler_total_log_check).2
  norm_num only at h ⊢
  exact h

end PseudoPrime.PrimeTestBounds.MillerRabin
