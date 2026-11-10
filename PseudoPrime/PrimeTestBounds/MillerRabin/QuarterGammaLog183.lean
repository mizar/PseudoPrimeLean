/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.LogTaylorBounds

/-! # Logarithm certificate at radius 183 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

-- Kernel reduction checks the independent rational logarithm certificate.
/-- Check an upper bound for `log (183²)`. -/
theorem quarter_gamma_log183_check :
    Analysis.rationalLogIntervalCheck 33489 15 32 0 (10419 / 1000) = true := by decide +kernel

/-- The logarithm at radius 183 is at most `10419/1000`. -/
theorem quarter_gamma_log183 : Real.log ((183 : ℝ) ^ 2) ≤ 10419 / 1000 := by
  have h := (Analysis.rationalLogIntervalCheck_sound quarter_gamma_log183_check).2
  norm_num only at h ⊢
  exact h

end PseudoPrime.PrimeTestBounds.MillerRabin
