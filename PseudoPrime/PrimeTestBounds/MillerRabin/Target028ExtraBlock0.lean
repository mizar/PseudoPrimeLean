/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028FiniteRows

/-! # Additional Euler prefix block 0 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational prime-power rows in additional block 0. -/
def target028ExtraData0 : ℕ → RefinedEulerAtom
  | 1009 => ⟨1009, 1, 6916713 / 1000000, 6916718 / 1000000, 0⟩
  | 1013 => ⟨1013, 1, 6920669 / 1000000, 6920674 / 1000000, 0⟩
  | 1019 => ⟨1019, 1, 6926575 / 1000000, 6926580 / 1000000, 0⟩
  | 1021 => ⟨1021, 1, 6928535 / 1000000, 6928540 / 1000000, 0⟩
  | 1024 => ⟨2, 10, 693145 / 1000000, 693150 / 1000000, 0⟩
  | 1031 => ⟨1031, 1, 6938282 / 1000000, 6938287 / 1000000, 0⟩
  | 1033 => ⟨1033, 1, 6940220 / 1000000, 6940225 / 1000000, 0⟩
  | 1039 => ⟨1039, 1, 6946011 / 1000000, 6946016 / 1000000, 0⟩
  | 1049 => ⟨1049, 1, 6955590 / 1000000, 6955595 / 1000000, 0⟩
  | 1051 => ⟨1051, 1, 6957495 / 1000000, 6957500 / 1000000, 0⟩
  | 1061 => ⟨1061, 1, 6966965 / 1000000, 6966970 / 1000000, 0⟩
  | 1063 => ⟨1063, 1, 6968848 / 1000000, 6968853 / 1000000, 0⟩
  | 1069 => ⟨1069, 1, 6974476 / 1000000, 6974481 / 1000000, 0⟩
  | 1087 => ⟨1087, 1, 6991174 / 1000000, 6991179 / 1000000, 0⟩
  | 1091 => ⟨1091, 1, 6994847 / 1000000, 6994852 / 1000000, 0⟩
  | 1093 => ⟨1093, 1, 6996679 / 1000000, 6996684 / 1000000, 0⟩
  | 1097 => ⟨1097, 1, 7000332 / 1000000, 7000337 / 1000000, 0⟩
  | 1103 => ⟨1103, 1, 7005787 / 1000000, 7005792 / 1000000, 0⟩
  | 1109 => ⟨1109, 1, 7011211 / 1000000, 7011216 / 1000000, 0⟩
  | 1117 => ⟨1117, 1, 7018399 / 1000000, 7018404 / 1000000, 0⟩
  | _ => ⟨2, 1, 0, 1, 0⟩

/-- Prime-power indices in additional block 0. -/
def target028ExtraSet0 : Finset ℕ :=
  {
    1009, 1013, 1019, 1021, 1024, 1031, 1033, 1039,
    1049, 1051, 1061, 1063, 1069, 1087, 1091, 1093,
    1097, 1103, 1109, 1117
  }

-- The finite block reduces at most twenty proposed prime-power certificates.
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Each logarithm interval uses 24 rational Taylor terms.
/-- Every additional block 0 row passes the Euler atom checker. -/
theorem target028_extra_check0 :
    ∀ n ∈ target028ExtraSet0, refinedEulerAtomCheck 24 n (target028ExtraData0 n) = true := by
  decide +kernel

-- Kernel reduction checks the finite set of indices in this block.
set_option maxRecDepth 1000000 in
/-- The indices in block 0 lie within its stated endpoints. -/
theorem target028_extra_range0 : ∀ n ∈ target028ExtraSet0, 1000 < n ∧ n ≤ 1117 := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
