/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030KorseltFastSearch

/-! # Uniform Korselt search for smallest factors from 100 to 161 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
-- The kernel evaluates the reordered bounded enumeration for this range.
/-- The reordered search has no candidate with smallest factor from 100 to
161. Early prime and valuation checks keep the certificate compact. -/
theorem target030_fast_candidates_100to162 : target030FastRange 100 62 = [] := by decide +kernel

/-- The original complete candidate search also has no candidate from 100 to
161, by inclusion in the checked reordered search. -/
theorem target030_candidates_100to162 : target030CandidateRange 100 62 = [] :=
  target030_range_empty_of_fast target030_fast_candidates_100to162

end PseudoPrime.PrimeTestBounds.MillerRabin
