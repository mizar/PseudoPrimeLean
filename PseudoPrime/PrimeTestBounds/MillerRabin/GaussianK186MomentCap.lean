/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighCompressedMoment

import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighCompressedMoment
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighNegativeMoment
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighProfileSign
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianLaplaceSignCell
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighKernelData

/-! # Compressed numerical certificates for K186 negative moments -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The compressed K186 zero-order charge is at most its proposed cap. -/
private theorem k186_charge_order_zero :
    highCompressedMomentCharge .k186 0 ≤ highCompressedMomentCap .k186 0 := by decide +kernel

/-- The compressed K186 first-order charge is at most its proposed cap. -/
private theorem k186_charge_order_one :
    highCompressedMomentCharge .k186 1 ≤ highCompressedMomentCap .k186 1 := by decide +kernel

/-- The compressed K186 second-order charge is at most its proposed cap. -/
private theorem k186_charge_order_two :
    highCompressedMomentCharge .k186 2 ≤ highCompressedMomentCap .k186 2 := by decide +kernel

/-- All three compressed K186 charges lie below their stated rational caps. -/
theorem k186_compressed_charge_le (j : Fin 3) :
    highCompressedMomentCharge .k186 j ≤ highCompressedMomentCap .k186 j := by
  refine Fin.cases k186_charge_order_zero (fun i ↦ ?_) j
  refine Fin.cases k186_charge_order_one (fun k ↦ ?_) i
  rw [Fin.eq_zero k]
  exact k186_charge_order_two

end PseudoPrime.PrimeTestBounds.MillerRabin
