/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.LogTaylorBounds

/-! # Lower logarithmic endpoint for the first Gamma pole -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

-- Kernel reduction checks the finite rational logarithm certificate.
/-- The lower logarithm endpoint is checked independently of the upper
endpoint certificate. -/
theorem quarter_gamma_log_lower_check :
    Analysis.rationalLogIntervalCheck 32400 15 32 (83 / 8) 11 = true := by decide +kernel

/-- The lower endpoint `180²` has logarithm at least `83/8`. -/
theorem quarter_gamma_log_lower : (83 / 8 : ℝ) ≤ Real.log 32400 := by
  have h := (Analysis.rationalLogIntervalCheck_sound quarter_gamma_log_lower_check).1
  norm_num only at h ⊢
  exact h

end PseudoPrime.PrimeTestBounds.MillerRabin
