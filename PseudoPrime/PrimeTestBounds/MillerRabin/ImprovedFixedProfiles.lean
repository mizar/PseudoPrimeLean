/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.TriangularProfileBounds

/-! # Rational profiles for short intervals between adaptive triangular cutoffs -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The coefficient `3869 / 10000` profile is valid from logarithmic scale fifty billion.
The rational fields certify all local, triple and large-index budgets. -/
noncomputable def improvedProfile03869 : TriangularProfile where
  C := 3869 / 10000
  T := 50000000000
  a := 622011 / 1000000
  m := 20491 / 1000
  v := 223606
  b := 98171 / 15625
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

/-- The coefficient `222 / 625` profile is valid from logarithmic scale seventy billion.
The rational fields certify all local, triple and large-index budgets. -/
noncomputable def improvedProfile03552 : TriangularProfile where
  C := 222 / 625
  T := 70000000000
  a := 119197 / 200000
  m := 21257 / 1000
  v := 264575
  b := 2257507 / 500000
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

/-- The coefficient `1567 / 5000` profile is valid from logarithmic scale 150 billion.
The rational fields certify all local, triple and large-index budgets. -/
noncomputable def improvedProfile03134 : TriangularProfile where
  C := 1567 / 5000
  T := 150000000000
  a := 27991 / 50000
  m := 116 / 5
  v := 387298
  b := 2055261 / 1000000
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
