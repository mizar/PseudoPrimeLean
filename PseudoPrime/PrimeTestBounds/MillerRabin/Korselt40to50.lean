/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.KorseltSearch

/-! # Uniform Korselt search for smallest factors from 40 to 49 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

set_option maxRecDepth 32768 in
-- The kernel evaluates the bounded parameters in this factor range.
/-- The bounded search with smallest factor from 40 to 49 contains exactly
the two listed parameter triples. -/
theorem korselt_candidates_40to50 :
    korseltCandidateRange 40 10 = [(41, 22, 72), (43, 26, 126)] := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
