/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.LogTaylorBounds

/-! # Logarithm certificate at radius 180 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

-- Kernel reduction checks the independent rational logarithm certificate.
/-- Check an upper bound for `log (180²)`. -/
theorem quarter_gamma_log180_check :
    Analysis.rationalLogIntervalCheck 32400 15 32 0 (5193 / 500) = true := by decide +kernel

/-- The logarithm at the first endpoint is at most `5193/500`. -/
theorem quarter_gamma_log180 : Real.log ((180 : ℝ) ^ 2) ≤ 5193 / 500 := by
  have h := (Analysis.rationalLogIntervalCheck_sound quarter_gamma_log180_check).2
  norm_num only at h ⊢
  exact h

end PseudoPrime.PrimeTestBounds.MillerRabin
