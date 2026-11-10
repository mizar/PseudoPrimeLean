/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.TruncatedEulerCertificates3

/-! # Negative-power endpoint for the Euler total -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

-- Exact rational reduction checks this negative-power endpoint independently.
/-- The large Euler cutoff has inverse power below `1/1000000`. -/
theorem quarter_euler_total_power_check :
    AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 1000000000000 0 (1 / 1000000) 29 50 =
      true := by
  decide +kernel

/-- The inverse power of the large cutoff is at most `1/1000000`. -/
theorem quarter_euler_total_power : (1000000000000 : ℝ) ^ (-(29 / 50 : ℝ)) ≤ 1 / 1000000 := by
  have h :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
        quarter_euler_total_power_check).2
  norm_num only at h ⊢
  exact h

end PseudoPrime.PrimeTestBounds.MillerRabin
