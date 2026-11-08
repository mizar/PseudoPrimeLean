/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028ExtraBlock0

/-! # Additional Euler prefix block 1 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational prime-power rows in additional block 1. -/
def target028ExtraData1 : ℕ → RefinedEulerAtom
  | 1123 => ⟨1123, 1, 7023756 / 1000000, 7023761 / 1000000, 0⟩
  | 1129 => ⟨1129, 1, 7029085 / 1000000, 7029090 / 1000000, 0⟩
  | 1151 => ⟨1151, 1, 7048384 / 1000000, 7048389 / 1000000, 0⟩
  | 1153 => ⟨1153, 1, 7050120 / 1000000, 7050125 / 1000000, 0⟩
  | 1163 => ⟨1163, 1, 7058756 / 1000000, 7058761 / 1000000, 0⟩
  | 1171 => ⟨1171, 1, 7065611 / 1000000, 7065616 / 1000000, 0⟩
  | 1181 => ⟨1181, 1, 7074114 / 1000000, 7074119 / 1000000, 0⟩
  | 1187 => ⟨1187, 1, 7079182 / 1000000, 7079187 / 1000000, 0⟩
  | 1193 => ⟨1193, 1, 7084224 / 1000000, 7084229 / 1000000, 0⟩
  | 1201 => ⟨1201, 1, 7090907 / 1000000, 7090912 / 1000000, 0⟩
  | 1213 => ⟨1213, 1, 7100849 / 1000000, 7100854 / 1000000, 0⟩
  | 1217 => ⟨1217, 1, 7104142 / 1000000, 7104147 / 1000000, 0⟩
  | 1223 => ⟨1223, 1, 7109060 / 1000000, 7109065 / 1000000, 0⟩
  | 1229 => ⟨1229, 1, 7113954 / 1000000, 7113959 / 1000000, 0⟩
  | 1231 => ⟨1231, 1, 7115580 / 1000000, 7115585 / 1000000, 0⟩
  | 1237 => ⟨1237, 1, 7120442 / 1000000, 7120447 / 1000000, 0⟩
  | 1249 => ⟨1249, 1, 7130096 / 1000000, 7130101 / 1000000, 0⟩
  | 1259 => ⟨1259, 1, 7138071 / 1000000, 7138076 / 1000000, 0⟩
  | 1277 => ⟨1277, 1, 7152266 / 1000000, 7152271 / 1000000, 0⟩
  | 1279 => ⟨1279, 1, 7153831 / 1000000, 7153836 / 1000000, 0⟩
  | _ => ⟨2, 1, 0, 1, 0⟩

/-- Prime-power indices in additional block 1. -/
def target028ExtraSet1 : Finset ℕ :=
  {
    1123, 1129, 1151, 1153, 1163, 1171, 1181, 1187,
    1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237,
    1249, 1259, 1277, 1279
  }

-- The finite block reduces at most twenty proposed prime-power certificates.
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Each logarithm interval uses 24 rational Taylor terms.
/-- Every additional block 1 row passes the Euler atom checker. -/
theorem target028_extra_check1 :
    ∀ n ∈ target028ExtraSet1, refinedEulerAtomCheck 24 n (target028ExtraData1 n) = true := by
  decide +kernel

-- Kernel reduction checks the finite set of indices in this block.
set_option maxRecDepth 1000000 in
/-- The indices in block 1 lie within its stated endpoints. -/
theorem target028_extra_range1 : ∀ n ∈ target028ExtraSet1, 1117 < n ∧ n ≤ 1279 := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
