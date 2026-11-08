/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Fine61Supply
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Fine59Counts

/-! # Extended weighted counts through 61 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

-- Accessing the certified 456-entry row needs additional recursion depth.
set_option maxRecDepth 65536 in
/-- The checked count through 59 and a suffix count give the budget 462 count. -/
theorem target028_fine61_count462 : weightedPrimeCount id target028Fine61Weights 462 = 1129 := by
  change weightedPrimeCount id (243 :: target028Fine59Weights) 462 = 1129
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [target028_fine59_count462, weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, dite_true, dite_false]
  change 1089 + weightedPrimeCount id (241 :: target028Fine53Weights) 219 = 1129
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, dite_true, dite_false]
  change
    1089 +
        weightedPrimeCount id
          [235, 228, 220, 222, 214, 41, 65, 95, 115, 142, 152, 168, 174, 185, 199, 203] 219 =
      1129
  rw [target028_fine53_suffix0 219 (by decide)]
  rfl

-- Accessing the certified 456-entry row needs additional recursion depth.
set_option maxRecDepth 65536 in
/-- The checked count through 59 and a suffix count give the budget 466 count. -/
theorem target028_fine61_count466 : weightedPrimeCount id target028Fine61Weights 466 = 1183 := by
  change weightedPrimeCount id (243 :: target028Fine59Weights) 466 = 1183
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [target028_fine59_count466, weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, dite_true, dite_false]
  change 1140 + weightedPrimeCount id (241 :: target028Fine53Weights) 223 = 1183
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, dite_true, dite_false]
  change
    1140 +
        weightedPrimeCount id
          [235, 228, 220, 222, 214, 41, 65, 95, 115, 142, 152, 168, 174, 185, 199, 203] 223 =
      1183
  rw [target028_fine53_suffix0 223 (by decide)]
  rfl

-- Accessing the certified 456-entry row needs additional recursion depth.
set_option maxRecDepth 65536 in
/-- The checked count through 59 and a suffix count give the budget 469 count. -/
theorem target028_fine61_count469 : weightedPrimeCount id target028Fine61Weights 469 = 1226 := by
  change weightedPrimeCount id (243 :: target028Fine59Weights) 469 = 1226
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [target028_fine59_count469, weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, dite_true, dite_false]
  change 1180 + weightedPrimeCount id (241 :: target028Fine53Weights) 226 = 1226
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, dite_true, dite_false]
  change
    1180 +
        weightedPrimeCount id
          [235, 228, 220, 222, 214, 41, 65, 95, 115, 142, 152, 168, 174, 185, 199, 203] 226 =
      1226
  rw [target028_fine53_suffix0 226 (by decide)]
  rfl

-- Accessing the certified 456-entry row needs additional recursion depth.
set_option maxRecDepth 65536 in
/-- The checked count through 59 and a suffix count give the budget 471 count. -/
theorem target028_fine61_count471 : weightedPrimeCount id target028Fine61Weights 471 = 1255 := by
  change weightedPrimeCount id (243 :: target028Fine59Weights) 471 = 1255
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [target028_fine59_count471, weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, dite_true, dite_false]
  change 1208 + weightedPrimeCount id (241 :: target028Fine53Weights) 228 = 1255
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, dite_true, dite_false]
  change
    1208 +
        weightedPrimeCount id
          [235, 228, 220, 222, 214, 41, 65, 95, 115, 142, 152, 168, 174, 185, 199, 203] 228 =
      1255
  rw [target028_fine53_suffix0 228 (by decide)]
  rfl

end PseudoPrime.PrimeTestBounds.MillerRabin
