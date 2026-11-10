/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleEulerCertificate

/-! # Additional Euler prefix block 11 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational prime-power rows in additional block 11. -/
def target028ExtraData11 : ℕ → RefinedEulerAtom
  | 2609 => ⟨2609, 1, 7866720 / 1000000, 7866725 / 1000000, 0⟩
  | 2617 => ⟨2617, 1, 7869781 / 1000000, 7869786 / 1000000, 0⟩
  | 2621 => ⟨2621, 1, 7871309 / 1000000, 7871314 / 1000000, 0⟩
  | 2633 => ⟨2633, 1, 7875877 / 1000000, 7875882 / 1000000, 0⟩
  | 2647 => ⟨2647, 1, 7881180 / 1000000, 7881185 / 1000000, 0⟩
  | 2657 => ⟨2657, 1, 7884950 / 1000000, 7884955 / 1000000, 0⟩
  | 2659 => ⟨2659, 1, 7885703 / 1000000, 7885708 / 1000000, 0⟩
  | 2663 => ⟨2663, 1, 7887206 / 1000000, 7887211 / 1000000, 0⟩
  | 2671 => ⟨2671, 1, 7890206 / 1000000, 7890211 / 1000000, 0⟩
  | 2677 => ⟨2677, 1, 7892450 / 1000000, 7892455 / 1000000, 0⟩
  | 2683 => ⟨2683, 1, 7894688 / 1000000, 7894693 / 1000000, 0⟩
  | 2687 => ⟨2687, 1, 7896178 / 1000000, 7896183 / 1000000, 0⟩
  | 2689 => ⟨2689, 1, 7896922 / 1000000, 7896927 / 1000000, 0⟩
  | 2693 => ⟨2693, 1, 7898409 / 1000000, 7898414 / 1000000, 0⟩
  | 2699 => ⟨2699, 1, 7900634 / 1000000, 7900639 / 1000000, 0⟩
  | _ => ⟨2, 1, 0, 1, 0⟩

/-- Prime-power indices in additional block 11. -/
def target028ExtraSet11 : Finset ℕ :=
  {
    2609, 2617, 2621, 2633, 2647, 2657, 2659, 2663,
    2671, 2677, 2683, 2687, 2689, 2693, 2699
  }

-- The finite block reduces at most twenty proposed prime-power certificates.
set_option maxRecDepth 1000000 in
-- Each logarithm interval uses 24 rational Taylor terms.
/-- Every additional block 11 row passes the Euler atom checker. -/
theorem target028_extra_check11 :
    ∀ n ∈ target028ExtraSet11, refinedEulerAtomCheck 24 n (target028ExtraData11 n) = true := by
  decide +kernel

-- Kernel reduction checks the finite set of indices in this block.
set_option maxRecDepth 1000000 in
/-- The indices in block 11 lie within its stated endpoints. -/
theorem target028_extra_range11 : ∀ n ∈ target028ExtraSet11, 2593 < n ∧ n ≤ 2699 := by
  decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
