/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.KorseltFastSearch

/-! # Uniform Korselt search for smallest factors from 100 to 161 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
-- The kernel evaluates the reordered bounded enumeration for this range.
/-- The reordered search has no candidate with smallest factor from 100 to
161. Early prime and valuation checks keep the certificate compact. -/
theorem korselt_fast_candidates_100to162 : korseltFastRange 100 62 = [] := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
