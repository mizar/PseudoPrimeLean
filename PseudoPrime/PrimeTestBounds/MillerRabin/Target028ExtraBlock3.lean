/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleEulerCertificate

/-! # Additional Euler prefix block 3 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational prime-power rows in additional block 3. -/
def target028ExtraData3 : ℕ → RefinedEulerAtom
  | 1429 => ⟨1429, 1, 7264728 / 1000000, 7264733 / 1000000, 0⟩
  | 1433 => ⟨1433, 1, 7267523 / 1000000, 7267528 / 1000000, 0⟩
  | 1439 => ⟨1439, 1, 7271701 / 1000000, 7271706 / 1000000, 0⟩
  | 1447 => ⟨1447, 1, 7277245 / 1000000, 7277250 / 1000000, 0⟩
  | 1451 => ⟨1451, 1, 7280006 / 1000000, 7280011 / 1000000, 0⟩
  | 1453 => ⟨1453, 1, 7281383 / 1000000, 7281388 / 1000000, 0⟩
  | 1459 => ⟨1459, 1, 7285504 / 1000000, 7285509 / 1000000, 0⟩
  | 1471 => ⟨1471, 1, 7293695 / 1000000, 7293700 / 1000000, 0⟩
  | 1481 => ⟨1481, 1, 7300470 / 1000000, 7300475 / 1000000, 0⟩
  | 1483 => ⟨1483, 1, 7301820 / 1000000, 7301825 / 1000000, 0⟩
  | 1487 => ⟨1487, 1, 7304513 / 1000000, 7304518 / 1000000, 0⟩
  | 1489 => ⟨1489, 1, 7305858 / 1000000, 7305863 / 1000000, 0⟩
  | 1493 => ⟨1493, 1, 7308540 / 1000000, 7308545 / 1000000, 0⟩
  | 1499 => ⟨1499, 1, 7312551 / 1000000, 7312556 / 1000000, 0⟩
  | 1511 => ⟨1511, 1, 7320524 / 1000000, 7320529 / 1000000, 0⟩
  | 1523 => ⟨1523, 1, 7328435 / 1000000, 7328440 / 1000000, 0⟩
  | 1531 => ⟨1531, 1, 7333674 / 1000000, 7333679 / 1000000, 0⟩
  | 1543 => ⟨1543, 1, 7341481 / 1000000, 7341486 / 1000000, 0⟩
  | 1549 => ⟨1549, 1, 7345362 / 1000000, 7345367 / 1000000, 0⟩
  | 1553 => ⟨1553, 1, 7347941 / 1000000, 7347946 / 1000000, 0⟩
  | _ => ⟨2, 1, 0, 1, 0⟩

/-- Prime-power indices in additional block 3. -/
def target028ExtraSet3 : Finset ℕ :=
  {
    1429, 1433, 1439, 1447, 1451, 1453, 1459, 1471,
    1481, 1483, 1487, 1489, 1493, 1499, 1511, 1523,
    1531, 1543, 1549, 1553
  }

-- The finite block reduces at most twenty proposed prime-power certificates.
set_option maxRecDepth 1000000 in
-- Each logarithm interval uses 24 rational Taylor terms.
/-- Every additional block 3 row passes the Euler atom checker. -/
theorem target028_extra_check3 :
    ∀ n ∈ target028ExtraSet3, refinedEulerAtomCheck 24 n (target028ExtraData3 n) = true := by
  decide +kernel

-- Kernel reduction checks the finite set of indices in this block.
set_option maxRecDepth 1000000 in
/-- The indices in block 3 lie within its stated endpoints. -/
theorem target028_extra_range3 : ∀ n ∈ target028ExtraSet3, 1427 < n ∧ n ≤ 1553 := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
