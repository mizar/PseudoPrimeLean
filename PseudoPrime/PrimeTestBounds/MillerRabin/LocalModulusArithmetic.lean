/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Tactic.IntervalCases

/-! # Small odd moduli in local Miller–Rabin reductions -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- An odd divisor between 2 and 4 is 3. This handles the local modulus below
the range of the log-square witness theorem. -/
theorem odd_divisor_eq_three_of_lt_five {n m : ℕ} (ho : Odd n) (hm : 2 ≤ m) (hd : m ∣ n)
    (hsmall : m < 5) : m = 3 := by
  have hodd := Odd.of_dvd_nat ho hd
  interval_cases m
  · exact False.elim ((by decide : ¬Odd 2) hodd)
  · rfl
  · exact False.elim ((by decide : ¬Odd 4) hodd)

end PseudoPrime.PrimeTestBounds.MillerRabin
