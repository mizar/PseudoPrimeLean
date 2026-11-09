/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed1849Data
public import PseudoPrime.PrimeTestBounds.MillerRabin.WeightedPrimeCountGroup

/-! # Grouped count lower bounds through 1849 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

set_option maxRecDepth 32768 in
/-- The established budget-500 lower bound combines with the additional
209 labels of cost 76, giving a multichoose multiple at budget `500 + 76k`.
This supplies lower counts without a new row per added prime. -/
theorem primeSeed1849_count_lower (k : ℕ) :
    Nat.choose (209 + k) k * 68854718408873 ≤
      weightedPrimeCount id primeSeed1849Weights (500 + k * 76) := by
  have hbase := primeSeed373_count_lower 500 (by decide)
  have hb : 68854718408873 ≤ weightedPrimeCount id primeSeed373Weights 500 := by
    change primeSeed373Row14.getD 500 0 ≤ _ at hbase
    exact hbase
  have hg := weightedPrimeCount_group_lower 76 500 209 k primeSeed373Weights (by decide)
  exact (Nat.mul_le_mul_left (Nat.choose (209 + k) k) hb).trans hg

/-- For any certified base budget through 500, the 209 additional labels
supply a multichoose multiple of its lower count at the extended budget. -/
theorem primeSeed1849_group_lower (A k : ℕ) (hA : A ≤ 500) :
    Nat.choose (209 + k) k * primeSeed373Row14.getD A 0 ≤
      weightedPrimeCount id primeSeed1849Weights (A + k * 76) := by
  have hb := primeSeed373_count_lower A hA
  have hg := weightedPrimeCount_group_lower 76 A 209 k primeSeed373Weights (by decide)
  exact (Nat.mul_le_mul_left (Nat.choose (209 + k) k) hb).trans hg

end PseudoPrime.PrimeTestBounds.MillerRabin
