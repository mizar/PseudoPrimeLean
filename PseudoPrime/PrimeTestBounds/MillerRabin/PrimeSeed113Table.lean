/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed113

/-! # Composed weighted table through 113 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The six new rows followed by the existing checked 89-prime table. -/
def primeSeed113Rows : List (Array ℕ) :=
  [primeSeed113Row6, primeSeed113Row5, primeSeed113Row4, primeSeed113Row3, primeSeed113Row2,
      primeSeed113Row1, primeSeed89Row358] ++
    primeSeed89Tail358

/-- The composed table passes the recurrence checker by its existing row
certificates, without repeating the kernel reduction of the earlier table. -/
theorem primeSeed113_checked :
    weightedPrimeTableCheck 358 primeSeed113Weights primeSeed113Rows = true := by
  change
    (weightedPrimeRowCheck 48 358 primeSeed113Row5 primeSeed113Row6 &&
        (weightedPrimeRowCheck 47 358 primeSeed113Row4 primeSeed113Row5 &&
          (weightedPrimeRowCheck 47 358 primeSeed113Row3 primeSeed113Row4 &&
            (weightedPrimeRowCheck 47 358 primeSeed113Row2 primeSeed113Row3 &&
              (weightedPrimeRowCheck 47 358 primeSeed113Row1 primeSeed113Row2 &&
                (weightedPrimeRowCheck 46 358 primeSeed89Row358 primeSeed113Row1 &&
                  weightedPrimeTableCheck 358 primeSeed89Weights
                    (primeSeed89Row358 :: primeSeed89Tail358))))))) =
      true
  simp only [primeSeed113Check1, primeSeed113Check2, primeSeed113Check3, primeSeed113Check4,
    primeSeed113Check5, primeSeed113Check6, primeSeed89_checked358, Bool.true_and]

end PseudoPrime.PrimeTestBounds.MillerRabin
