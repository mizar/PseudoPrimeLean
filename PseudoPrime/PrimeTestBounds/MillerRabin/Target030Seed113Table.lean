/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030Seed113

/-! # Composed weighted table through 113 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The six new rows followed by the existing checked 89-prime table. -/
def target030Seed113Rows : List (Array ℕ) :=
  [target030Seed113Row6, target030Seed113Row5, target030Seed113Row4, target030Seed113Row3,
      target030Seed113Row2, target030Seed113Row1, target030Seed89Row358] ++
    target030Seed89Tail358

/-- The composed table passes the recurrence checker by its existing row
certificates, without repeating the kernel reduction of the earlier table. -/
theorem target030Seed113_checked :
    weightedPrimeTableCheck 358 target030Seed113Weights target030Seed113Rows = true := by
  change
    (weightedPrimeRowCheck 48 358 target030Seed113Row5 target030Seed113Row6 &&
        (weightedPrimeRowCheck 47 358 target030Seed113Row4 target030Seed113Row5 &&
          (weightedPrimeRowCheck 47 358 target030Seed113Row3 target030Seed113Row4 &&
            (weightedPrimeRowCheck 47 358 target030Seed113Row2 target030Seed113Row3 &&
              (weightedPrimeRowCheck 47 358 target030Seed113Row1 target030Seed113Row2 &&
                (weightedPrimeRowCheck 46 358 target030Seed89Row358 target030Seed113Row1 &&
                  weightedPrimeTableCheck 358 target030Seed89Weights
                    (target030Seed89Row358 :: target030Seed89Tail358))))))) =
      true
  simp only [target030Seed113Check1, target030Seed113Check2, target030Seed113Check3,
    target030Seed113Check4, target030Seed113Check5, target030Seed113Check6,
    target030Seed89_checked358, Bool.true_and]

end PseudoPrime.PrimeTestBounds.MillerRabin
