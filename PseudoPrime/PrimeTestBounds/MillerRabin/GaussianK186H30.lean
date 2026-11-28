/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighPrincipalReflected
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186MomentSign
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186MomentCap

/-! # The certified K186 H30 coefficient -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The K186 principal and reflected corrections share a coefficient
at most 78548, by the three compressed negative-moment certificates. -/
theorem k186_h30_charge_le : highH30Charge .k186 ≤ 78548 := by
  exact high_h30_le_compressed_cap .k186 k186_compressed_sign k186_compressed_charge_le

end PseudoPrime.PrimeTestBounds.MillerRabin
