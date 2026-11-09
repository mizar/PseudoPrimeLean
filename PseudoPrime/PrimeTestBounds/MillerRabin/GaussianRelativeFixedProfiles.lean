/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianRelativeProfiles

/-! Fixed relative Gaussian profile certificates. -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The common triple certificate proves coefficient 0.28237 from thirty billion. -/
noncomputable def gaussianRelativeCommon : GaussianRelativeProfile where
  C := 28237 / 100000
  T := 30000000000
  a := 36669 / 100000
  v := 170000
  entry := by norm_num only
  root := by norm_num only
  square := by norm_num only
  upper := by norm_num only
  fourth := by norm_num only [and_self]
  margin := by norm_num only

/-- The sharper triple certificate proves coefficient 0.2823622 from 1.82 trillion. -/
noncomputable def gaussianRelativeSharper : GaussianRelativeProfile where
  C := 1411811 / 5000000
  T := 1820000000000
  a := 36668541 / 100000000
  v := 1340000
  entry := by norm_num only
  root := by norm_num only
  square := by norm_num only
  upper := by norm_num only
  fourth := by norm_num only [and_self]
  margin := by norm_num only

end PseudoPrime.PrimeTestBounds.MillerRabin
