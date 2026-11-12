/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Data.List.Basic

/-! # Weighted prime data through 89 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The distinct prime labels through 89 extend the supply through 61. -/
def primeSeed89Primes : List ℕ :=
  (([2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43]) ++ [47, 53, 59, 61]) ++
    [67, 71, 73, 79, 83, 89]

/-- Scaled logarithmic weights extend the previous supply through 89. -/
def primeSeed89Weight (p : ℕ) : ℕ :=
  if p ≤ 61 then
    (if p ≤ 43 then
      (if p ≤ 19 then
        (if p ≤ 2 then 7
        else
          if p ≤ 3 then 11
          else
            if p ≤ 5 then 17
            else if p ≤ 7 then 20 else if p ≤ 11 then 24 else if p ≤ 13 then 26 else 30)
      else if p ≤ 23 then 32 else if p ≤ 31 then 35 else 38)
    else if p ≤ 47 then 39 else if p ≤ 53 then 40 else if p ≤ 59 then 41 else 42)
  else if p ≤ 73 then 43 else if p ≤ 79 then 44 else 45

/-- Ordered weights for the prime labels through 89. -/
def primeSeed89Weights : List ℕ :=
  [7, 11, 17, 20, 24, 26, 30, 30, 32, 35, 35, 38, 38, 38, 39, 40, 41, 42, 43, 43, 43, 44, 45, 45]

end PseudoPrime.PrimeTestBounds.MillerRabin
