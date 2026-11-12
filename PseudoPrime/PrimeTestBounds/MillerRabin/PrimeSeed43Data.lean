/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Data.List.Basic

/-! # Weighted prime data through 43 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The primes through 43 used as distinct labels in the weighted family. -/
def primeSeed43Primes : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43]

/-- Integer logarithm weights scaled by ten for the supply through 43.
The first eight weights reuse the previous supply; larger primes share three
certified cutoff bounds. -/
def primeSeed43Weight (p : ℕ) : ℕ :=
  if p ≤ 19 then
    (if p ≤ 2 then 7
    else
      if p ≤ 3 then 11
      else
        if p ≤ 5 then 17
        else if p ≤ 7 then 20 else if p ≤ 11 then 24 else if p ≤ 13 then 26 else 30)
  else if p ≤ 23 then 32 else if p ≤ 31 then 35 else 38

/-- The list of scaled weights assigned to the ordered prime labels. -/
def primeSeed43Weights : List ℕ :=
  [7, 11, 17, 20, 24, 26, 30, 30, 32, 35, 35, 38, 38, 38]

end PseudoPrime.PrimeTestBounds.MillerRabin
