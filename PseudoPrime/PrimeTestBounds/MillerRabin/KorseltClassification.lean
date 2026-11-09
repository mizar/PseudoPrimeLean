/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.KorseltAggregate
public import PseudoPrime.PrimeTestBounds.MillerRabin.Korselt100to162

/-! # Complete bounded uniform Korselt triple classification -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The original complete candidate search also has no candidate from 100 to
161, by inclusion in the checked reordered search. -/
theorem korselt_candidates_100to162 : korseltCandidateRange 100 62 = [] :=
  korselt_range_empty_of_fast korselt_fast_candidates_100to162

/-- The final empty factor range from 100 to 161 completes the bounded search.
The accumulated candidates are exactly those already found below 50. -/
theorem korselt_candidates_all : korseltCandidateRows 162 = korseltCandidateRows 50 := by
  have h := korselt_rows_add_empty 100 62 korselt_candidates_100to162
  norm_num only at h
  exact h.trans korselt_candidates_below100

/-- Every uniform Korselt triple at most `2^22` is one of the six explicit
products. Ordered factor extraction and the parameter search prove that the
finite list covers every input, rather than merely checking selected examples. -/
theorem uniformKorselt_le_pow22_cases {n : ℕ} (hu : UniformKorseltTriple n) (hbound : n ≤ 2 ^ 22) :
    n ∈ [8911, 314821, 29341, 1024651, 410041, 1152271] := by
  obtain ⟨p, q, r, a, hp, hq, hr, hpq, hqr, hn, hpbound, ha, hap, hdiv, hadiv, hrform⟩ :=
    uniformKorselt_search_complete hu hbound
  have hp162 : p < 162 := by linarith only [hpbound]
  exact uniformKorselt_cases_of_rows hu hbound hn hp hq hr hpq hqr hp162 korselt_candidates_all

end PseudoPrime.PrimeTestBounds.MillerRabin
