/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Data.List.Basic

/-! # Weighted prime data through 199 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The supply through 199 extends the earlier distinct prime labels. -/
def primeSeed199Primes : List ℕ :=
  [199, 197, 193, 191, 181, 179, 173, 167, 163, 157, 151, 149, 139, 137, 131, 127] ++
    ([113, 109, 107, 103, 101, 97] ++
      ((([2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43]) ++ [47, 53, 59, 61]) ++
        [67, 71, 73, 79, 83, 89]))

/-- Scaled logarithmic weights extend the supply through 113. -/
def primeSeed199Weight (p : ℕ) : ℕ :=
  if p ≤ 113 then
    (if p ≤ 89 then
      (if p ≤ 61 then
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
      else if p ≤ 73 then 43 else if p ≤ 79 then 44 else 45)
    else if p ≤ 97 then 46 else if p ≤ 109 then 47 else 48)
  else
    if p ≤ 131 then 49
    else if p ≤ 139 then 50 else if p ≤ 163 then 51 else if p ≤ 181 then 52 else 53

/-- Ordered scaled weights retain each prime label. -/
def primeSeed199Weights : List ℕ :=
  [53, 53, 53, 53, 52, 52, 52, 52, 51, 51, 51, 51, 50, 50, 49, 49] ++
    ([48, 47, 47, 47, 47, 46] ++
      ([7, 11, 17, 20, 24, 26, 30, 30, 32, 35, 35, 38, 38, 38, 39, 40, 41, 42, 43, 43, 43, 44, 45,
        45]))

end PseudoPrime.PrimeTestBounds.MillerRabin
