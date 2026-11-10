/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Fine53Suffix

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Fine59Supply

/-! # Counts for the extended prime supply -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

-- The certified row has 456 entries.
set_option maxRecDepth 65536 in
/-- The budget 453 count follows from the two certified rows after adding 59. -/
theorem target028_fine59_count453 : weightedPrimeCount id target028Fine59Weights 453 = 978 := by
  change
    weightedPrimeCount id
        (241 :: [235, 228, 220, 222, 214, 41, 65, 95, 115, 142, 152, 168, 174, 185, 199, 203]) 453 =
      978
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [target028_fine53_suffix0 453 (by decide), weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, dite_true, dite_false]
  rw [target028_fine53_suffix0 212 (by decide)]
  rfl

-- The certified rows have 456 entries and are used to extend the budget.
set_option maxRecDepth 65536 in
/-- The suffix recurrences extend the exact count to budget 456. -/
theorem target028_fine59_count456 : weightedPrimeCount id target028Fine59Weights 456 = 1014 := by
  change
    weightedPrimeCount id
        (241 :: [235, 228, 220, 222, 214, 41, 65, 95, 115, 142, 152, 168, 174, 185, 199, 203]) 456 =
      1014
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  rw [target028_fine53_suffix15 253 (by decide)]
  rw [target028_fine53_suffix14 257 (by decide)]
  rw [target028_fine53_suffix13 271 (by decide)]
  rw [target028_fine53_suffix12 282 (by decide)]
  rw [target028_fine53_suffix11 288 (by decide)]
  rw [target028_fine53_suffix10 304 (by decide)]
  rw [target028_fine53_suffix9 314 (by decide)]
  rw [target028_fine53_suffix8 341 (by decide)]
  rw [target028_fine53_suffix7 361 (by decide)]
  rw [target028_fine53_suffix6 391 (by decide)]
  rw [target028_fine53_suffix5 415 (by decide)]
  rw [target028_fine53_suffix4 242 (by decide)]
  rw [target028_fine53_suffix3 234 (by decide)]
  rw [target028_fine53_suffix2 236 (by decide)]
  rw [target028_fine53_suffix1 228 (by decide)]
  rw [target028_fine53_suffix0 221 (by decide)]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, dite_true, dite_false]
  rw [target028_fine53_suffix0 215 (by decide)]
  rfl

-- The certified rows have 456 entries and are used to extend the budget.
set_option maxRecDepth 65536 in
/-- The suffix recurrences extend the exact count to budget 458. -/
theorem target028_fine59_count458 : weightedPrimeCount id target028Fine59Weights 458 = 1037 := by
  change
    weightedPrimeCount id
        (241 :: [235, 228, 220, 222, 214, 41, 65, 95, 115, 142, 152, 168, 174, 185, 199, 203]) 458 =
      1037
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  rw [target028_fine53_suffix15 255 (by decide)]
  rw [target028_fine53_suffix14 259 (by decide)]
  rw [target028_fine53_suffix13 273 (by decide)]
  rw [target028_fine53_suffix12 284 (by decide)]
  rw [target028_fine53_suffix11 290 (by decide)]
  rw [target028_fine53_suffix10 306 (by decide)]
  rw [target028_fine53_suffix9 316 (by decide)]
  rw [target028_fine53_suffix8 343 (by decide)]
  rw [target028_fine53_suffix7 363 (by decide)]
  rw [target028_fine53_suffix6 393 (by decide)]
  rw [target028_fine53_suffix5 417 (by decide)]
  rw [target028_fine53_suffix4 244 (by decide)]
  rw [target028_fine53_suffix3 236 (by decide)]
  rw [target028_fine53_suffix2 238 (by decide)]
  rw [target028_fine53_suffix1 230 (by decide)]
  rw [target028_fine53_suffix0 223 (by decide)]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, dite_true, dite_false]
  rw [target028_fine53_suffix0 217 (by decide)]
  rfl

-- The certified rows have 456 entries and are used to extend the budget.
set_option maxRecDepth 65536 in
/-- The suffix recurrences extend the exact count to budget 460. -/
theorem target028_fine59_count460 : weightedPrimeCount id target028Fine59Weights 460 = 1063 := by
  change
    weightedPrimeCount id
        (241 :: [235, 228, 220, 222, 214, 41, 65, 95, 115, 142, 152, 168, 174, 185, 199, 203]) 460 =
      1063
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  rw [target028_fine53_suffix15 257 (by decide)]
  rw [target028_fine53_suffix14 261 (by decide)]
  rw [target028_fine53_suffix13 275 (by decide)]
  rw [target028_fine53_suffix12 286 (by decide)]
  rw [target028_fine53_suffix11 292 (by decide)]
  rw [target028_fine53_suffix10 308 (by decide)]
  rw [target028_fine53_suffix9 318 (by decide)]
  rw [target028_fine53_suffix8 345 (by decide)]
  rw [target028_fine53_suffix7 365 (by decide)]
  rw [target028_fine53_suffix6 395 (by decide)]
  rw [target028_fine53_suffix5 419 (by decide)]
  rw [target028_fine53_suffix4 246 (by decide)]
  rw [target028_fine53_suffix3 238 (by decide)]
  rw [target028_fine53_suffix2 240 (by decide)]
  rw [target028_fine53_suffix1 232 (by decide)]
  rw [target028_fine53_suffix0 225 (by decide)]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, dite_true, dite_false]
  rw [target028_fine53_suffix0 219 (by decide)]
  rfl

-- The certified rows have 456 entries and are used to extend the budget.
set_option maxRecDepth 65536 in
/-- The suffix recurrences extend the exact count to budget 462. -/
theorem target028_fine59_count462 : weightedPrimeCount id target028Fine59Weights 462 = 1089 := by
  change
    weightedPrimeCount id
        (241 :: [235, 228, 220, 222, 214, 41, 65, 95, 115, 142, 152, 168, 174, 185, 199, 203]) 462 =
      1089
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  rw [target028_fine53_suffix15 259 (by decide)]
  rw [target028_fine53_suffix14 263 (by decide)]
  rw [target028_fine53_suffix13 277 (by decide)]
  rw [target028_fine53_suffix12 288 (by decide)]
  rw [target028_fine53_suffix11 294 (by decide)]
  rw [target028_fine53_suffix10 310 (by decide)]
  rw [target028_fine53_suffix9 320 (by decide)]
  rw [target028_fine53_suffix8 347 (by decide)]
  rw [target028_fine53_suffix7 367 (by decide)]
  rw [target028_fine53_suffix6 397 (by decide)]
  rw [target028_fine53_suffix5 421 (by decide)]
  rw [target028_fine53_suffix4 248 (by decide)]
  rw [target028_fine53_suffix3 240 (by decide)]
  rw [target028_fine53_suffix2 242 (by decide)]
  rw [target028_fine53_suffix1 234 (by decide)]
  rw [target028_fine53_suffix0 227 (by decide)]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, dite_true, dite_false]
  rw [target028_fine53_suffix0 221 (by decide)]
  rfl

-- The certified rows have 456 entries and are used to extend the budget.
set_option maxRecDepth 65536 in
/-- The suffix recurrences extend the exact count to budget 466. -/
theorem target028_fine59_count466 : weightedPrimeCount id target028Fine59Weights 466 = 1140 := by
  change
    weightedPrimeCount id
        (241 :: [235, 228, 220, 222, 214, 41, 65, 95, 115, 142, 152, 168, 174, 185, 199, 203]) 466 =
      1140
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  rw [target028_fine53_suffix15 263 (by decide)]
  rw [target028_fine53_suffix14 267 (by decide)]
  rw [target028_fine53_suffix13 281 (by decide)]
  rw [target028_fine53_suffix12 292 (by decide)]
  rw [target028_fine53_suffix11 298 (by decide)]
  rw [target028_fine53_suffix10 314 (by decide)]
  rw [target028_fine53_suffix9 324 (by decide)]
  rw [target028_fine53_suffix8 351 (by decide)]
  rw [target028_fine53_suffix7 371 (by decide)]
  rw [target028_fine53_suffix6 401 (by decide)]
  rw [target028_fine53_suffix5 425 (by decide)]
  rw [target028_fine53_suffix4 252 (by decide)]
  rw [target028_fine53_suffix3 244 (by decide)]
  rw [target028_fine53_suffix2 246 (by decide)]
  rw [target028_fine53_suffix1 238 (by decide)]
  rw [target028_fine53_suffix0 231 (by decide)]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, dite_true, dite_false]
  rw [target028_fine53_suffix0 225 (by decide)]
  rfl

-- The certified rows have 456 entries and are used to extend the budget.
set_option maxRecDepth 65536 in
/-- The suffix recurrences extend the exact count to budget 469. -/
theorem target028_fine59_count469 : weightedPrimeCount id target028Fine59Weights 469 = 1180 := by
  change
    weightedPrimeCount id
        (241 :: [235, 228, 220, 222, 214, 41, 65, 95, 115, 142, 152, 168, 174, 185, 199, 203]) 469 =
      1180
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  rw [target028_fine53_suffix15 266 (by decide)]
  rw [target028_fine53_suffix14 270 (by decide)]
  rw [target028_fine53_suffix13 284 (by decide)]
  rw [target028_fine53_suffix12 295 (by decide)]
  rw [target028_fine53_suffix11 301 (by decide)]
  rw [target028_fine53_suffix10 317 (by decide)]
  rw [target028_fine53_suffix9 327 (by decide)]
  rw [target028_fine53_suffix8 354 (by decide)]
  rw [target028_fine53_suffix7 374 (by decide)]
  rw [target028_fine53_suffix6 404 (by decide)]
  rw [target028_fine53_suffix5 428 (by decide)]
  rw [target028_fine53_suffix4 255 (by decide)]
  rw [target028_fine53_suffix3 247 (by decide)]
  rw [target028_fine53_suffix2 249 (by decide)]
  rw [target028_fine53_suffix1 241 (by decide)]
  rw [target028_fine53_suffix0 234 (by decide)]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, dite_true, dite_false]
  rw [target028_fine53_suffix0 228 (by decide)]
  rfl

-- The certified rows have 456 entries and are used to extend the budget.
set_option maxRecDepth 65536 in
/-- The suffix recurrences extend the exact count to budget 471. -/
theorem target028_fine59_count471 : weightedPrimeCount id target028Fine59Weights 471 = 1208 := by
  change
    weightedPrimeCount id
        (241 :: [235, 228, 220, 222, 214, 41, 65, 95, 115, 142, 152, 168, 174, 185, 199, 203]) 471 =
      1208
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, Nat.reduceSub, dite_true]
  rw [weightedPrimeCount.eq_def]
  rw [target028_fine53_suffix15 268 (by decide)]
  rw [target028_fine53_suffix14 272 (by decide)]
  rw [target028_fine53_suffix13 286 (by decide)]
  rw [target028_fine53_suffix12 297 (by decide)]
  rw [target028_fine53_suffix11 303 (by decide)]
  rw [target028_fine53_suffix10 319 (by decide)]
  rw [target028_fine53_suffix9 329 (by decide)]
  rw [target028_fine53_suffix8 356 (by decide)]
  rw [target028_fine53_suffix7 376 (by decide)]
  rw [target028_fine53_suffix6 406 (by decide)]
  rw [target028_fine53_suffix5 430 (by decide)]
  rw [target028_fine53_suffix4 257 (by decide)]
  rw [target028_fine53_suffix3 249 (by decide)]
  rw [target028_fine53_suffix2 251 (by decide)]
  rw [target028_fine53_suffix1 243 (by decide)]
  rw [target028_fine53_suffix0 236 (by decide)]
  rw [weightedPrimeCount.eq_def]
  norm_num only [id_eq, Nat.reduceLT, dite_true, dite_false]
  rw [target028_fine53_suffix0 230 (by decide)]
  rfl

end PseudoPrime.PrimeTestBounds.MillerRabin
