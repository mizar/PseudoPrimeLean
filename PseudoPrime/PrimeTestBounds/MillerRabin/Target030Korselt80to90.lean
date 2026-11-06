/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030KorseltSearch

/-! # Uniform Korselt search for smallest factors from 80 to 89 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
-- The kernel evaluates the bounded parameters in this factor range.
/-- No candidate has smallest factor between 80 and 89. -/
theorem target030_candidates_80to90 : target030CandidateRange 80 10 = [] := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
