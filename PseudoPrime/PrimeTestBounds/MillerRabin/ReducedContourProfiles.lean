/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.ReducedContourCore

/-! # First reduced-contour triangular profile -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The coefficient `39 / 100` triangular profile has entrance `2 * 10 ^ 8`.
Its rational fields certify the reduced contour budget, radius floors and
strict comparison margin, for use by the local and large-index branches. -/
noncomputable def reducedProfile039 : ReducedContourCore where
  C := 39 / 100
  T := 200000000
  a := 624499 / 1000000
  m := 10281 / 1000
  v := 14142
  b := 49897 / 8000
  entry := by norm_num only
  root := by norm_num only
  localBudget := by norm_num only
  square := by norm_num only
  upper := by norm_num only
  root16 := by norm_num only [and_self]
  fourth := by norm_num only [and_self]
  cost := by norm_num only
  margin := by norm_num only

/-- The reduced-contour certificate for coefficient `161 / 500` at scale five hundred million. -/
noncomputable def reducedProfile0322 : ReducedContourCore where
  C := 161 / 500
  T := 500000000
  a := 11349 / 20000
  m := 1424 / 125
  v := 22360
  b := 154869 / 62500
  entry := by norm_num only
  root := by norm_num only
  localBudget := by norm_num only
  square := by norm_num only
  upper := by norm_num only
  root16 := by norm_num only [and_self]
  fourth := by norm_num only [and_self]
  cost := by norm_num only
  margin := by norm_num only

/-- The reduced-contour certificate for coefficient `3 / 10` at scale one billion. -/
noncomputable def reducedProfile030 : ReducedContourCore where
  C := 3 / 10
  T := 1000000000
  a := 273861 / 500000
  m := 1546 / 125
  v := 31622
  b := 1182293 / 1000000
  entry := by norm_num only
  root := by norm_num only
  localBudget := by norm_num only
  square := by norm_num only
  upper := by norm_num only
  root16 := by norm_num only [and_self]
  fourth := by norm_num only [and_self]
  cost := by norm_num only
  margin := by norm_num only

/-- The reduced-contour certificate for coefficient `71 / 250` at scale five billion. -/
noncomputable def reducedProfile0284 : ReducedContourCore where
  C := 71 / 250
  T := 5000000000
  a := 133229 / 250000
  m := 15073 / 1000
  v := 70710
  b := 9971 / 50000
  entry := by norm_num only
  root := by norm_num only
  localBudget := by norm_num only
  square := by norm_num only
  upper := by norm_num only
  root16 := by norm_num only [and_self]
  fourth := by norm_num only [and_self]
  cost := by norm_num only
  margin := by norm_num only

/-- The reduced-contour certificate for coefficient `28237 / 100000` at scale thirty billion. -/
noncomputable def reducedProfile028237 : ReducedContourCore where
  C := 28237 / 100000
  T := 30000000000
  a := 66423 / 125000
  m := 377 / 20
  v := 173205
  b := 5331 / 200000
  entry := by norm_num only
  root := by norm_num only
  localBudget := by norm_num only
  square := by norm_num only
  upper := by norm_num only
  root16 := by norm_num only [and_self]
  fourth := by norm_num only [and_self]
  cost := by norm_num only
  margin := by norm_num only

end PseudoPrime.PrimeTestBounds.MillerRabin
