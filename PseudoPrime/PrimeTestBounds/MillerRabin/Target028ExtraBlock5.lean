/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleEulerCertificate

/-! # Additional Euler prefix block 5 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational prime-power rows in additional block 5. -/
def target028ExtraData5 : ℕ → RefinedEulerAtom
  | 1697 => ⟨1697, 1, 7436615 / 1000000, 7436620 / 1000000, 0⟩
  | 1699 => ⟨1699, 1, 7437793 / 1000000, 7437798 / 1000000, 0⟩
  | 1709 => ⟨1709, 1, 7443661 / 1000000, 7443666 / 1000000, 0⟩
  | 1721 => ⟨1721, 1, 7450658 / 1000000, 7450663 / 1000000, 0⟩
  | 1723 => ⟨1723, 1, 7451820 / 1000000, 7451825 / 1000000, 0⟩
  | 1733 => ⟨1733, 1, 7457607 / 1000000, 7457612 / 1000000, 0⟩
  | 1741 => ⟨1741, 1, 7462212 / 1000000, 7462217 / 1000000, 0⟩
  | 1747 => ⟨1747, 1, 7465653 / 1000000, 7465658 / 1000000, 0⟩
  | 1753 => ⟨1753, 1, 7469081 / 1000000, 7469086 / 1000000, 0⟩
  | 1759 => ⟨1759, 1, 7472498 / 1000000, 7472503 / 1000000, 0⟩
  | 1777 => ⟨1777, 1, 7482679 / 1000000, 7482684 / 1000000, 0⟩
  | 1783 => ⟨1783, 1, 7486050 / 1000000, 7486055 / 1000000, 0⟩
  | 1787 => ⟨1787, 1, 7488291 / 1000000, 7488296 / 1000000, 0⟩
  | 1789 => ⟨1789, 1, 7489410 / 1000000, 7489415 / 1000000, 0⟩
  | 1801 => ⟨1801, 1, 7496095 / 1000000, 7496100 / 1000000, 0⟩
  | 1811 => ⟨1811, 1, 7501632 / 1000000, 7501637 / 1000000, 0⟩
  | 1823 => ⟨1823, 1, 7508236 / 1000000, 7508241 / 1000000, 0⟩
  | 1831 => ⟨1831, 1, 7512615 / 1000000, 7512620 / 1000000, 0⟩
  | 1847 => ⟨1847, 1, 7521315 / 1000000, 7521320 / 1000000, 0⟩
  | 1849 => ⟨43, 2, 3761198 / 1000000, 3761203 / 1000000, 0⟩
  | _ => ⟨2, 1, 0, 1, 0⟩

/-- Prime-power indices in additional block 5. -/
def target028ExtraSet5 : Finset ℕ :=
  {
    1697, 1699, 1709, 1721, 1723, 1733, 1741, 1747,
    1753, 1759, 1777, 1783, 1787, 1789, 1801, 1811,
    1823, 1831, 1847, 1849
  }

-- The finite block reduces at most twenty proposed prime-power certificates.
set_option maxRecDepth 1000000 in
-- Each logarithm interval uses 24 rational Taylor terms.
/-- Every additional block 5 row passes the Euler atom checker. -/
theorem target028_extra_check5 :
    ∀ n ∈ target028ExtraSet5, refinedEulerAtomCheck 24 n (target028ExtraData5 n) = true := by
  decide +kernel

-- Kernel reduction checks the finite set of indices in this block.
set_option maxRecDepth 1000000 in
/-- The indices in block 5 lie within its stated endpoints. -/
theorem target028_extra_range5 : ∀ n ∈ target028ExtraSet5, 1693 < n ∧ n ≤ 1849 := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
