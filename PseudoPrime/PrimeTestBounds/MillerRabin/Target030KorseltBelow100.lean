/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030KorseltBelow90
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030Korselt90to100

/-! # Combined uniform Korselt search below smallest factor 100 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The empty factor range from 90 to 99 adds no candidates to the six already
found below 50. -/
theorem target030_candidates_below100 : target030CandidateRows 100 = target030CandidateRows 50 := by
  have h := target030_rows_add_empty 90 10 target030_candidates_90to100
  norm_num only at h
  exact h.trans target030_candidates_below90

/-- A bounded uniform Korselt triple with ordered smallest factor below 100 is
one of the six explicit products from the checked candidate list. -/
theorem uniformKorselt_below100_cases {n p q r : ℕ} (hu : UniformKorseltTriple n)
    (hbound : n ≤ 2 ^ 22) (hn : n = p * q * r) (hp : p.Prime) (hq : q.Prime) (hrp : r.Prime)
    (hpq : p < q) (hqr : q < r) (hsmall : p < 100) :
    n ∈ [8911, 314821, 29341, 1024651, 410041, 1152271] :=
  uniformKorselt_cases_of_rows hu hbound hn hp hq hrp hpq hqr hsmall target030_candidates_below100

end PseudoPrime.PrimeTestBounds.MillerRabin
