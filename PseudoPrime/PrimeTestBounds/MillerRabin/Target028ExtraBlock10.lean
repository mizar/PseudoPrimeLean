/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028ExtraBlock9

/-! # Additional Euler prefix block 10 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational prime-power rows in additional block 10. -/
def target028ExtraData10 : ℕ → RefinedEulerAtom
  | 2417 => ⟨2417, 1, 7790280 / 1000000, 7790285 / 1000000, 0⟩
  | 2423 => ⟨2423, 1, 7792759 / 1000000, 7792764 / 1000000, 0⟩
  | 2437 => ⟨2437, 1, 7798521 / 1000000, 7798526 / 1000000, 0⟩
  | 2441 => ⟨2441, 1, 7800161 / 1000000, 7800166 / 1000000, 0⟩
  | 2447 => ⟨2447, 1, 7802616 / 1000000, 7802621 / 1000000, 0⟩
  | 2459 => ⟨2459, 1, 7807508 / 1000000, 7807513 / 1000000, 0⟩
  | 2467 => ⟨2467, 1, 7810756 / 1000000, 7810761 / 1000000, 0⟩
  | 2473 => ⟨2473, 1, 7813185 / 1000000, 7813190 / 1000000, 0⟩
  | 2477 => ⟨2477, 1, 7814801 / 1000000, 7814806 / 1000000, 0⟩
  | 2503 => ⟨2503, 1, 7825243 / 1000000, 7825248 / 1000000, 0⟩
  | 2521 => ⟨2521, 1, 7832408 / 1000000, 7832413 / 1000000, 0⟩
  | 2531 => ⟨2531, 1, 7836367 / 1000000, 7836372 / 1000000, 0⟩
  | 2539 => ⟨2539, 1, 7839523 / 1000000, 7839528 / 1000000, 0⟩
  | 2543 => ⟨2543, 1, 7841097 / 1000000, 7841102 / 1000000, 0⟩
  | 2549 => ⟨2549, 1, 7843454 / 1000000, 7843459 / 1000000, 0⟩
  | 2551 => ⟨2551, 1, 7844238 / 1000000, 7844243 / 1000000, 0⟩
  | 2557 => ⟨2557, 1, 7846587 / 1000000, 7846592 / 1000000, 0⟩
  | 2579 => ⟨2579, 1, 7855155 / 1000000, 7855160 / 1000000, 0⟩
  | 2591 => ⟨2591, 1, 7859797 / 1000000, 7859802 / 1000000, 0⟩
  | 2593 => ⟨2593, 1, 7860568 / 1000000, 7860573 / 1000000, 0⟩
  | _ => ⟨2, 1, 0, 1, 0⟩

/-- Prime-power indices in additional block 10. -/
def target028ExtraSet10 : Finset ℕ :=
  {
    2417, 2423, 2437, 2441, 2447, 2459, 2467, 2473,
    2477, 2503, 2521, 2531, 2539, 2543, 2549, 2551,
    2557, 2579, 2591, 2593
  }

-- The finite block reduces at most twenty proposed prime-power certificates.
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Each logarithm interval uses 24 rational Taylor terms.
/-- Every additional block 10 row passes the Euler atom checker. -/
theorem target028_extra_check10 :
    ∀ n ∈ target028ExtraSet10, refinedEulerAtomCheck 24 n (target028ExtraData10 n) = true := by
  decide +kernel

-- Kernel reduction checks the finite set of indices in this block.
set_option maxRecDepth 1000000 in
/-- The indices in block 10 lie within its stated endpoints. -/
theorem target028_extra_range10 : ∀ n ∈ target028ExtraSet10, 2411 < n ∧ n ≤ 2593 := by
  decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
