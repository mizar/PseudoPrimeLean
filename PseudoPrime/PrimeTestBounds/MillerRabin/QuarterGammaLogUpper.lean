/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.LogTaylorBounds

/-! # Upper logarithmic endpoint for the first Gamma pole -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

-- Kernel reduction checks the finite rational logarithm certificate.
/-- The upper logarithm endpoint is checked independently of the lower
endpoint certificate. -/
theorem quarter_gamma_log_upper_check :
    Analysis.rationalLogIntervalCheck 40000 15 32 10 (85 / 8) = true := by decide +kernel

/-- The upper endpoint `200²` has logarithm at most `85/8`. -/
theorem quarter_gamma_log_upper : Real.log 40000 ≤ (85 / 8 : ℝ) := by
  have h := (Analysis.rationalLogIntervalCheck_sound quarter_gamma_log_upper_check).2
  norm_num only at h ⊢
  exact h

end PseudoPrime.PrimeTestBounds.MillerRabin
