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

/-! # Compressed sign certificates for the K186 negative moments -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The zero-order K186 profile passes the compressed sign checks. -/
private theorem k186_sign_order_zero : highCompressedSignCheck .k186 0 = true := by decide +kernel

/-- The first derivative of the K186 profile passes the compressed sign checks. -/
private theorem k186_sign_order_one : highCompressedSignCheck .k186 1 = true := by decide +kernel

/-- The second derivative of the K186 profile passes the compressed sign checks. -/
private theorem k186_sign_order_two : highCompressedSignCheck .k186 2 = true := by decide +kernel

/-- All three K186 moments have signed certificates for their compressed plans. -/
theorem k186_compressed_sign (j : Fin 3) : highCompressedSignCheck .k186 j = true := by
  refine Fin.cases k186_sign_order_zero (fun i ↦ ?_) j
  refine Fin.cases k186_sign_order_one (fun k ↦ ?_) i
  rw [Fin.eq_zero k]
  exact k186_sign_order_two

end PseudoPrime.PrimeTestBounds.MillerRabin
