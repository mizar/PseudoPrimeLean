/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028ExtraBlock3

/-! # Additional Euler prefix block 4 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational prime-power rows in additional block 4. -/
def target028ExtraData4 : ℕ → RefinedEulerAtom
  | 1559 => ⟨1559, 1, 7351797 / 1000000, 7351802 / 1000000, 0⟩
  | 1567 => ⟨1567, 1, 7356916 / 1000000, 7356921 / 1000000, 0⟩
  | 1571 => ⟨1571, 1, 7359465 / 1000000, 7359470 / 1000000, 0⟩
  | 1579 => ⟨1579, 1, 7364545 / 1000000, 7364550 / 1000000, 0⟩
  | 1583 => ⟨1583, 1, 7367075 / 1000000, 7367080 / 1000000, 0⟩
  | 1597 => ⟨1597, 1, 7375880 / 1000000, 7375885 / 1000000, 0⟩
  | 1601 => ⟨1601, 1, 7378381 / 1000000, 7378386 / 1000000, 0⟩
  | 1607 => ⟨1607, 1, 7382122 / 1000000, 7382127 / 1000000, 0⟩
  | 1609 => ⟨1609, 1, 7383366 / 1000000, 7383371 / 1000000, 0⟩
  | 1613 => ⟨1613, 1, 7385849 / 1000000, 7385854 / 1000000, 0⟩
  | 1619 => ⟨1619, 1, 7389561 / 1000000, 7389566 / 1000000, 0⟩
  | 1621 => ⟨1621, 1, 7390796 / 1000000, 7390801 / 1000000, 0⟩
  | 1627 => ⟨1627, 1, 7394491 / 1000000, 7394496 / 1000000, 0⟩
  | 1637 => ⟨1637, 1, 7400618 / 1000000, 7400623 / 1000000, 0⟩
  | 1657 => ⟨1657, 1, 7412762 / 1000000, 7412767 / 1000000, 0⟩
  | 1663 => ⟨1663, 1, 7416376 / 1000000, 7416381 / 1000000, 0⟩
  | 1667 => ⟨1667, 1, 7418778 / 1000000, 7418783 / 1000000, 0⟩
  | 1669 => ⟨1669, 1, 7419977 / 1000000, 7419982 / 1000000, 0⟩
  | 1681 => ⟨41, 2, 3713570 / 1000000, 3713575 / 1000000, 0⟩
  | 1693 => ⟨1693, 1, 7434255 / 1000000, 7434260 / 1000000, 0⟩
  | _ => ⟨2, 1, 0, 1, 0⟩

/-- Prime-power indices in additional block 4. -/
def target028ExtraSet4 : Finset ℕ :=
  {
    1559, 1567, 1571, 1579, 1583, 1597, 1601, 1607,
    1609, 1613, 1619, 1621, 1627, 1637, 1657, 1663,
    1667, 1669, 1681, 1693
  }

-- The finite block reduces at most twenty proposed prime-power certificates.
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Each logarithm interval uses 24 rational Taylor terms.
/-- Every additional block 4 row passes the Euler atom checker. -/
theorem target028_extra_check4 :
    ∀ n ∈ target028ExtraSet4, refinedEulerAtomCheck 24 n (target028ExtraData4 n) = true := by
  decide +kernel

-- Kernel reduction checks the finite set of indices in this block.
set_option maxRecDepth 1000000 in
/-- The indices in block 4 lie within its stated endpoints. -/
theorem target028_extra_range4 : ∀ n ∈ target028ExtraSet4, 1553 < n ∧ n ≤ 1693 := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
