/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ExponentialFixedPointConversions
public import PseudoPrime.Analysis.ExponentialFixedPointExecution

/-! # Exponential lower certificate for the first Gamma pole -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

-- Kernel reduction checks the 64-step fixed-point certificate.
/-- A fixed-point Taylor certificate for the lower exponential endpoint.
The bound is checked independently of the upper endpoint certificate. -/
theorem quarter_gamma_exp_lower_check :
    1300000 ≤ Analysis.expFixedPointSignedLowerFast (-53) 8 1000000000 64 := by decide +kernel

/-- The exponential factor at the right endpoint `53/4` is at least
`13/10000`. The certified fixed-point lower bound supplies the comparison. -/
theorem quarter_gamma_exp_lower : (13 / 10000 : ℝ) ≤ Real.exp (-(53 / 8 : ℝ)) := by
  have h :=
    Analysis.exp_fixed_signed_lower_div (-53) 8 1000000000 64 (by norm_num only) (by norm_num only)
      (by norm_num only)
  have hcheck := quarter_gamma_exp_lower_check
  rw [Analysis.expFixedPointSignedLowerFast_eq] at hcheck
  have hc : (1300000 : ℝ) ≤ (Analysis.expFixedPointSignedLower (-53) 8 1000000000 64 : ℝ) := by
    exact_mod_cast hcheck
  norm_num only at h ⊢
  linarith only [h, hc]

end PseudoPrime.PrimeTestBounds.MillerRabin
