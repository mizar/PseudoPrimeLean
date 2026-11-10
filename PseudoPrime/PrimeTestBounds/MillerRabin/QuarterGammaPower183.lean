/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.TruncatedEulerCertificates3

/-! # Negative power certificate at radius 183 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

-- Kernel reduction checks the independent rational power certificate.
/-- Check an upper bound for `(183²)^(-27/25)`. -/
theorem quarter_gamma_power183_check :
    AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 33489 0 (12975 / 1000000000) 27 25 =
      true := by
  decide +kernel

/-- The negative power at radius 183 is at most `12975/1000000000`. -/
theorem quarter_gamma_power183 : ((183 : ℝ) ^ 2) ^ (-(27 / 25 : ℝ)) ≤ 12975 / 1000000000 := by
  have h :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
        quarter_gamma_power183_check).2
  norm_num only at h ⊢
  exact h

end PseudoPrime.PrimeTestBounds.MillerRabin
