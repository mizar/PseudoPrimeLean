/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.TruncatedEulerCertificates3

/-! # Negative power certificate at radius 180 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

-- Kernel reduction checks the independent rational power certificate.
/-- Check an upper bound for `(180²)^(-27/25)`. -/
theorem quarter_gamma_power180_check :
    AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 32400 0 (269 / 20000000) 27 25 =
      true := by
  decide +kernel

/-- The negative power at the first endpoint is at most `269/20000000`. -/
theorem quarter_gamma_power180 : ((180 : ℝ) ^ 2) ^ (-(27 / 25 : ℝ)) ≤ 269 / 20000000 := by
  have h :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
        quarter_gamma_power180_check).2
  norm_num only at h ⊢
  exact h

end PseudoPrime.PrimeTestBounds.MillerRabin
