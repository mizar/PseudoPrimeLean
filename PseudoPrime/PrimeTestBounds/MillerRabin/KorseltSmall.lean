/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.KorseltSearch

/-! # Smallest-factor block of the uniform Korselt search -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
-- The kernel evaluates the bounded parameter enumeration in this block.
/-- The complete bounded parameter search with smallest factor below 20 has
exactly these four candidates. This checks the integer conditions directly. -/
theorem korselt_candidates_below20 :
    korseltCandidateRows 20 = [(7, 2, 18), (13, 2, 60), (13, 8, 36), (19, 14, 198)] := by
  decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
