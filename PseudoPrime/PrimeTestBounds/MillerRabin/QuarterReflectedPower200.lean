/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.TruncatedEulerCertificates3

/-! # Negative-power lower endpoint at 200 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

-- Kernel reduction checks the rational endpoint independently.
/-- A rational certificate places the inverse power of 40000 above `1/100000`. -/
theorem quarter_reflected_power200_check :
    AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 40000 (1 / 100000) 1 27 25 =
      true := by
  decide +kernel

/-- The inverse power at the final cutoff is at least `1/100000`. -/
theorem quarter_reflected_power200 : (1 / 100000 : ℝ) ≤ (40000 : ℝ) ^ (-(27 / 25 : ℝ)) := by
  have h :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
        quarter_reflected_power200_check).1
  norm_num only at h ⊢
  exact h

end PseudoPrime.PrimeTestBounds.MillerRabin
