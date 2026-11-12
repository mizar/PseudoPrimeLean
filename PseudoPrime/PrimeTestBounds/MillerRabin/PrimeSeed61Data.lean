/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Data.List.Basic

/-! # Weighted prime data through 61 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The primes through 61 as distinct labels extending the supply through 43. -/
def primeSeed61Primes : List ℕ :=
  ([2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43]) ++ [47, 53, 59, 61]

/-- Integer logarithm weights scaled by ten for the supply through 61. The
previous weights are preserved and each new prime has a certified upper bound. -/
def primeSeed61Weight (p : ℕ) : ℕ :=
  if p ≤ 43 then
    (if p ≤ 19 then
      (if p ≤ 2 then 7
      else
        if p ≤ 3 then 11
        else
          if p ≤ 5 then 17
          else if p ≤ 7 then 20 else if p ≤ 11 then 24 else if p ≤ 13 then 26 else 30)
    else if p ≤ 23 then 32 else if p ≤ 31 then 35 else 38)
  else if p ≤ 47 then 39 else if p ≤ 53 then 40 else if p ≤ 59 then 41 else 42

/-- The ordered list of scaled weights for the prime supply through 61. -/
def primeSeed61Weights : List ℕ :=
  [7, 11, 17, 20, 24, 26, 30, 30, 32, 35, 35, 38, 38, 38, 39, 40, 41, 42]

end PseudoPrime.PrimeTestBounds.MillerRabin
