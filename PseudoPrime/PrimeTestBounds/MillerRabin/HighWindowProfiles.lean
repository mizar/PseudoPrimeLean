/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.TriangularProfiles

/-! # Rational certificates for high-window Miller–Rabin bounds -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A coefficient 323/1000 profile valid from logarithmic scale 120 billion.
The rational fields certify the hypotheses of the triangular witness theorem. -/
noncomputable def highWindowP0323 : TriangularProfile where
  C := 323 / 1000
  T := 120000000000
  a := 568330 / 1000000
  m := 22605 / 1000
  v := 346410
  b := 2597216 / 1000000
  entry := by norm_num only
  root := by norm_num only
  localBudget := by norm_num only
  square := by norm_num only
  upper := by norm_num only
  root16 := by norm_num only [and_self]
  fourth := by norm_num only [and_self]
  cost := by norm_num only
  triple := by exact Or.inl (by norm_num only)
  margin := by norm_num only

/-- A coefficient 37/125 profile valid from logarithmic scale 300 billion.
The rational fields certify the hypotheses of the triangular witness theorem. -/
noncomputable def highWindowP0296 : TriangularProfile where
  C := 37 / 125
  T := 300000000000
  a := 544058 / 1000000
  m := 25211 / 1000
  v := 547722
  b := 973056 / 1000000
  entry := by norm_num only
  root := by norm_num only
  localBudget := by norm_num only
  square := by norm_num only
  upper := by norm_num only
  root16 := by norm_num only [and_self]
  fourth := by norm_num only [and_self]
  cost := by norm_num only
  triple := by exact Or.inl (by norm_num only)
  margin := by norm_num only

/-- A coefficient 36/125 profile valid from logarithmic scale 600 billion.
The rational fields certify the hypotheses of the triangular witness theorem. -/
noncomputable def highWindowP0288 : TriangularProfile where
  C := 36 / 125
  T := 600000000000
  a := 536656 / 1000000
  m := 27446 / 1000
  v := 774596
  b := 453073 / 1000000
  entry := by norm_num only
  root := by norm_num only
  localBudget := by norm_num only
  square := by norm_num only
  upper := by norm_num only
  root16 := by norm_num only [and_self]
  fourth := by norm_num only [and_self]
  cost := by norm_num only
  triple := by exact Or.inl (by norm_num only)
  margin := by norm_num only

/-- A profile with coefficient 423/1000 from logarithmic scale thirty-eight billion.
Its rational parameters certify the triangular witness hypotheses. -/
noncomputable def highWindowP0423 : TriangularProfile where
  C := 423 / 1000
  T := 38000000000
  a := 650384 / 1000000
  m := 19912 / 1000
  v := 194935
  b := 8136282 / 1000000
  entry := by norm_num only
  root := by norm_num only
  localBudget := by norm_num only
  square := by norm_num only
  upper := by norm_num only
  root16 := by norm_num only [and_self]
  fourth := by norm_num only [and_self]
  cost := by norm_num only
  triple := by exact Or.inl (by norm_num only)
  margin := by norm_num only

/-- A profile with coefficient two fifths from logarithmic scale forty-five billion.
The rational parameters certify the hypotheses of the triangular witness theorem. -/
noncomputable def highWindowP040 : TriangularProfile where
  C := 2 / 5
  T := 45000000000
  a := 632455 / 1000000
  m := 20266 / 1000
  v := 212132
  b := 6941993 / 1000000
  entry := by norm_num only
  root := by norm_num only
  localBudget := by norm_num only
  square := by norm_num only
  upper := by norm_num only
  root16 := by norm_num only [and_self]
  fourth := by norm_num only [and_self]
  cost := by norm_num only
  triple := by exact Or.inl (by norm_num only)
  margin := by norm_num only

/-- A profile with coefficient 369/1000 from logarithmic scale sixty billion.
Its rational parameters certify the triangular witness hypotheses. -/
noncomputable def highWindowP0369 : TriangularProfile where
  C := 369 / 1000
  T := 60000000000
  a := 607453 / 1000000
  m := 20902 / 1000
  v := 244948
  b := 5255845 / 1000000
  entry := by norm_num only
  root := by norm_num only
  localBudget := by norm_num only
  square := by norm_num only
  upper := by norm_num only
  root16 := by norm_num only [and_self]
  fourth := by norm_num only [and_self]
  cost := by norm_num only
  triple := by exact Or.inl (by norm_num only)
  margin := by norm_num only

/-- A profile with coefficient 173/500 from logarithmic scale eighty billion.
Its rational parameters certify the triangular witness hypotheses. -/
noncomputable def highWindowP0346 : TriangularProfile where
  C := 173 / 500
  T := 80000000000
  a := 588217 / 1000000
  m := 21581 / 1000
  v := 282842
  b := 3942714 / 1000000
  entry := by norm_num only
  root := by norm_num only
  localBudget := by norm_num only
  square := by norm_num only
  upper := by norm_num only
  root16 := by norm_num only [and_self]
  fourth := by norm_num only [and_self]
  cost := by norm_num only
  triple := by exact Or.inl (by norm_num only)
  margin := by norm_num only

end PseudoPrime.PrimeTestBounds.MillerRabin
