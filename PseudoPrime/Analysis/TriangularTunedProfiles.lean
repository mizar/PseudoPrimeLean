/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.TriangularProfiles

/-! # Tuned triangular certificates at unchanged entrances -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The coefficient-04603 certificate retains its existing entrance and improves its cutoff. -/
noncomputable def triangularP04603 : TriangularProfile where
  C := 4603 / 10000
  T := 30000000000
  a := 678454 / 1000000
  m := 19434 / 1000
  v := 173205
  b := 10122562 / 1000000
  entry := by norm_num only
  root := by norm_num only
  localBudget := by norm_num only
  square := by norm_num only
  upper := by norm_num only
  root16 := by norm_num only [and_self]
  fourth := by norm_num only [and_self]
  cost := by norm_num only
  triple := Or.inl (by norm_num only)
  margin := by norm_num only

/-- The coefficient-04145 certificate retains its existing entrance and improves its cutoff. -/
noncomputable def triangularP04145 : TriangularProfile where
  C := 4145 / 10000
  T := 40000000000
  a := 643816 / 1000000
  m := 20014 / 1000
  v := 200000
  b := 7768527 / 1000000
  entry := by norm_num only
  root := by norm_num only
  localBudget := by norm_num only
  square := by norm_num only
  upper := by norm_num only
  root16 := by norm_num only [and_self]
  fourth := by norm_num only [and_self]
  cost := by norm_num only
  triple := Or.inl (by norm_num only)
  margin := by norm_num only

/-- The coefficient-03315 certificate retains its existing entrance and improves its cutoff. -/
noncomputable def triangularP03315 : TriangularProfile where
  C := 3315 / 10000
  T := 100000000000
  a := 575760 / 1000000
  m := 22132 / 1000
  v := 316227
  b := 3142188 / 1000000
  entry := by norm_num only
  root := by norm_num only
  localBudget := by norm_num only
  square := by norm_num only
  upper := by norm_num only
  root16 := by norm_num only [and_self]
  fourth := by norm_num only [and_self]
  cost := by norm_num only
  triple := Or.inl (by norm_num only)
  margin := by norm_num only

/-- The coefficient-02992 certificate retains its existing entrance and improves its cutoff. -/
noncomputable def triangularP02992 : TriangularProfile where
  C := 2992 / 10000
  T := 250000000000
  a := 546991 / 1000000
  m := 24659 / 1000
  v := 500000
  b := 1187405 / 1000000
  entry := by norm_num only
  root := by norm_num only
  localBudget := by norm_num only
  square := by norm_num only
  upper := by norm_num only
  root16 := by norm_num only [and_self]
  fourth := by norm_num only [and_self]
  cost := by norm_num only
  triple := Or.inl (by norm_num only)
  margin := by norm_num only

/-- The coefficient-02891 certificate retains its existing entrance and improves its cutoff. -/
noncomputable def triangularP02891 : TriangularProfile where
  C := 2891 / 10000
  T := 500000000000
  a := 537680 / 1000000
  m := 26834 / 1000
  v := 707106
  b := 555029 / 1000000
  entry := by norm_num only
  root := by norm_num only
  localBudget := by norm_num only
  square := by norm_num only
  upper := by norm_num only
  root16 := by norm_num only [and_self]
  fourth := by norm_num only [and_self]
  cost := by norm_num only
  triple := Or.inl (by norm_num only)
  margin := by norm_num only

/-- The coefficient-028399 certificate retains its existing entrance and improves its cutoff. -/
noncomputable def triangularP028399 : TriangularProfile where
  C := 28399 / 100000
  T := 1080000000000
  a := 532907 / 1000000
  m := 29512 / 1000
  v := 1039230
  b := 235734 / 1000000
  entry := by norm_num only
  root := by norm_num only
  localBudget := by norm_num only
  square := by norm_num only
  upper := by norm_num only
  root16 := by norm_num only [and_self]
  fourth := by norm_num only [and_self]
  cost := by norm_num only
  triple := Or.inl (by norm_num only)
  margin := by norm_num only

/-- The coefficient-028289 certificate retains its existing entrance and improves its cutoff. -/
noncomputable def triangularP028289 : TriangularProfile where
  C := 28289 / 100000
  T := 1480000000000
  a := 531874 / 1000000
  m := 30690 / 1000
  v := 1216552
  b := 165740 / 1000000
  entry := by norm_num only
  root := by norm_num only
  localBudget := by norm_num only
  square := by norm_num only
  upper := by norm_num only
  root16 := by norm_num only [and_self]
  fourth := by norm_num only [and_self]
  cost := by norm_num only
  triple := Or.inl (by norm_num only)
  margin := by norm_num only

/-- The seven improved certificates in increasing entrance order. The eighth current
certificate is retained separately, with its existing coefficient and entrance. -/
noncomputable def triangularTunedProfile (i : Fin 7) : TriangularProfile :=
  match i.val with
  | 0 => triangularP04603
  | 1 => triangularP04145
  | 2 => triangularP03315
  | 3 => triangularP02992
  | 4 => triangularP02891
  | 5 => triangularP028399
  | _ => triangularP028289

end PseudoPrime.Analysis
