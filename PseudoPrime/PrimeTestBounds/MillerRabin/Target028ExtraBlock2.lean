/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028ExtraBlock1

/-! # Additional Euler prefix block 2 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational prime-power rows in additional block 2. -/
def target028ExtraData2 : ℕ → RefinedEulerAtom
  | 1283 => ⟨1283, 1, 7156954 / 1000000, 7156959 / 1000000, 0⟩
  | 1289 => ⟨1289, 1, 7161620 / 1000000, 7161625 / 1000000, 0⟩
  | 1291 => ⟨1291, 1, 7163170 / 1000000, 7163175 / 1000000, 0⟩
  | 1297 => ⟨1297, 1, 7167807 / 1000000, 7167812 / 1000000, 0⟩
  | 1301 => ⟨1301, 1, 7170886 / 1000000, 7170891 / 1000000, 0⟩
  | 1303 => ⟨1303, 1, 7172422 / 1000000, 7172427 / 1000000, 0⟩
  | 1307 => ⟨1307, 1, 7175487 / 1000000, 7175492 / 1000000, 0⟩
  | 1319 => ⟨1319, 1, 7184627 / 1000000, 7184632 / 1000000, 0⟩
  | 1321 => ⟨1321, 1, 7186142 / 1000000, 7186147 / 1000000, 0⟩
  | 1327 => ⟨1327, 1, 7190674 / 1000000, 7190679 / 1000000, 0⟩
  | 1331 => ⟨11, 3, 2397893 / 1000000, 2397898 / 1000000, 0⟩
  | 1361 => ⟨1361, 1, 7215973 / 1000000, 7215978 / 1000000, 0⟩
  | 1367 => ⟨1367, 1, 7220371 / 1000000, 7220376 / 1000000, 0⟩
  | 1369 => ⟨37, 2, 3610915 / 1000000, 3610920 / 1000000, 0⟩
  | 1373 => ⟨1373, 1, 7224751 / 1000000, 7224756 / 1000000, 0⟩
  | 1381 => ⟨1381, 1, 7230561 / 1000000, 7230566 / 1000000, 0⟩
  | 1399 => ⟨1399, 1, 7243510 / 1000000, 7243515 / 1000000, 0⟩
  | 1409 => ⟨1409, 1, 7250633 / 1000000, 7250638 / 1000000, 0⟩
  | 1423 => ⟨1423, 1, 7260520 / 1000000, 7260525 / 1000000, 0⟩
  | 1427 => ⟨1427, 1, 7263327 / 1000000, 7263332 / 1000000, 0⟩
  | _ => ⟨2, 1, 0, 1, 0⟩

/-- Prime-power indices in additional block 2. -/
def target028ExtraSet2 : Finset ℕ :=
  {
    1283, 1289, 1291, 1297, 1301, 1303, 1307, 1319,
    1321, 1327, 1331, 1361, 1367, 1369, 1373, 1381,
    1399, 1409, 1423, 1427
  }

-- The finite block reduces at most twenty proposed prime-power certificates.
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
-- Each logarithm interval uses 24 rational Taylor terms.
/-- Every additional block 2 row passes the Euler atom checker. -/
theorem target028_extra_check2 :
    ∀ n ∈ target028ExtraSet2, refinedEulerAtomCheck 24 n (target028ExtraData2 n) = true := by
  decide +kernel

-- Kernel reduction checks the finite set of indices in this block.
set_option maxRecDepth 1000000 in
/-- The indices in block 2 lie within its stated endpoints. -/
theorem target028_extra_range2 : ∀ n ∈ target028ExtraSet2, 1279 < n ∧ n ≤ 1427 := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
