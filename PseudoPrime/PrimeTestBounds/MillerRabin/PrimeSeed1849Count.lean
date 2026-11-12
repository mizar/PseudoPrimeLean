/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed1849Data
public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed373Data
import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed373Bounds
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
  have hb := primeSeed373_count_500
  have hg := weightedPrimeCount_group_lower 76 500 209 k primeSeed373Weights (by decide)
  exact (Nat.mul_le_mul_left (Nat.choose (209 + k) k) hb).trans hg

/-- Any lower bound for the base weighted count yields a grouped lower bound
for the 209 additional labels at the corresponding extended budget. -/
theorem primeSeed1849_group_lower (A k C : ℕ)
    (hb : C ≤ weightedPrimeCount id primeSeed373Weights A) :
    Nat.choose (209 + k) k * C ≤ weightedPrimeCount id primeSeed1849Weights (A + k * 76) := by
  have hg := weightedPrimeCount_group_lower 76 A 209 k primeSeed373Weights (by decide)
  exact (Nat.mul_le_mul_left (Nat.choose (209 + k) k) hb).trans hg

end PseudoPrime.PrimeTestBounds.MillerRabin
