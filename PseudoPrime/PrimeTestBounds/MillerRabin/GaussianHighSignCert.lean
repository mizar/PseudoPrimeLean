/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighProfileSign
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186ProfileCert
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK196ProfileCert

/-! # Integer sign certificates for the H28 boundaries -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Both manuscript boundaries pass the integer sign check used by the
finite negative moment estimate. -/
public theorem high_correction_profile_check (K : HighGaussianKernel) :
    highIntProfileSignCheck K (profileCorrectionEnd K) = true := by
  cases K
  · exact k186_profile_grid_check
  · exact k196_profile_grid_check

end PseudoPrime.PrimeTestBounds.MillerRabin
