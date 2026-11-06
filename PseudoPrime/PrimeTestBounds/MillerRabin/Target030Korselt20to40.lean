/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030KorseltSearch

/-! # Uniform Korselt search for smallest factors from 20 to 39 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
-- The kernel evaluates the bounded parameters in this factor range.
/-- There are no candidates whose smallest factor is between 20 and 39.
The finite checker evaluates all admissible quotient and divisor parameters. -/
theorem target030_candidates_20to40 : target030CandidateRange 20 20 = [] := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
