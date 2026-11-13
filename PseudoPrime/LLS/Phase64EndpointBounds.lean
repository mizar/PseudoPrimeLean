/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ExponentialRampSummation
import PseudoPrime.LLS.Phase64SharpAggregateBounds

/-! # Table-free finite endpoint bounds for the phase64 cell -/

public section

namespace PseudoPrime.LLS.Phase64EndpointCertificates

/-- The actual lower-endpoint ramp sum is at least 1514, unconditionally.
Combine the checked blocks with the generic fixed-point sum soundness theorem. -/
theorem phase64_ramp_endpoint_lower : (1514 : ℝ) ≤ exponentialRampMangoldtSum (163840 / 99) := by
  exact phase64_ramp_endpoint_lower_of_blocks ramp_blocks principal_blocks

/-- The actual range-40000 exponential sum at the upper endpoint is at most
1654, unconditionally. The per-index logarithm, exponential, support and rounding
facts are all certified by the independent kernel block checks and soundness proof. -/
theorem phase64_principal_endpoint_upper :
    (∑ n ∈ Finset.range 40000,
        Real.exp (-(n : ℝ) / (4096128001 / 2475000)) * ArithmeticFunction.vonMangoldt n) ≤
      (1654 : ℝ) := by
  exact principal_endpoint_upper_of_blocks principal_blocks

/-- The existing aggregate certificates imply the actual ramp is at least
1514.09083. Kernel-check only the sixteen aggregate caps and reuse their block proofs.
This sharpens the previous integer cap without adding a prime-power certificate. -/
theorem phase64_ramp_endpoint_lower_sharp :
    (151409083 / 100000 : ℝ) ≤ exponentialRampMangoldtSum (163840 / 99) := by
  have hc : 15140908300000 ≤ ∑ i ∈ Finset.range 16, rampCaps i := by decide +kernel
  have h := ramp_endpoint_lower_of_aggregate ramp_blocks principal_blocks hc
  norm_num only [Nat.cast_ofNat] at h ⊢
  exact h

/-- The existing certificates imply the actual truncated principal mass is
at most 1653.1667. Check only the thirty-two aggregate caps and reuse the certified
blocks. This recovers precision previously lost in the cap 1654. -/
theorem phase64_principal_endpoint_upper_sharp :
    (∑ n ∈ Finset.range 40000,
        Real.exp (-(n : ℝ) / (4096128001 / 2475000)) * ArithmeticFunction.vonMangoldt n) ≤
      (16531667 / 10000 : ℝ) := by
  have hc : (∑ i ∈ Finset.range 32, principalCaps i) ≤ 16531667000000 := by decide +kernel
  have h := principal_endpoint_upper_of_aggregate principal_blocks hc
  norm_num only [Nat.cast_ofNat] at h ⊢
  exact h

end PseudoPrime.LLS.Phase64EndpointCertificates
