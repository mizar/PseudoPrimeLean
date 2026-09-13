/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import Mathlib.Algebra.Group.Even
import Mathlib.Data.Nat.Sqrt
import PseudoPrime.PrimeTest.Basic

/-!
# Common small-input, parity, and square precheck

The precheck handles the values below `3`, all even values, and square values.
Odd nonsquare inputs at least `3` are left to the test-specific executable body.
-/

namespace PseudoPrime.PrimeTest

/--
Return the result determined before a test-specific primality computation.

The result is `false` below `2`, `true` at `2`, `false` for every other even
number or square, and `none` for odd nonsquare inputs at least `3`.
-/
def natIsSquare (n : ℕ) : Bool :=
  Nat.sqrt n ^ 2 == n

theorem natIsSquare_false_of_not_isSquare {n : ℕ} (hns : ¬IsSquare n) : natIsSquare n = false := by
  by_contra h
  apply hns
  apply (isSquare_iff_exists_sq n).mpr
  refine ⟨Nat.sqrt n, ?_⟩
  have htrue : natIsSquare n = true := Bool.eq_true_of_not_eq_false h
  simpa only [natIsSquare] using (beq_iff_eq.mp htrue).symm

def primalityPrecheck (n : ℕ) : Option Bool :=
  if n < 2 then some false
  else
    if n = 2 then some true
    else if Even n then some false else if natIsSquare n then some false else none

/-- The precheck rejects zero. -/
theorem primalityPrecheck_zero : primalityPrecheck 0 = some false := by rfl

/-- The precheck rejects one. -/
theorem primalityPrecheck_one : primalityPrecheck 1 = some false := by rfl

/-- The precheck accepts two. -/
theorem primalityPrecheck_two : primalityPrecheck 2 = some true := by rfl

/-- Every even input other than two is rejected by the precheck. -/
theorem primalityPrecheck_even_false {n : ℕ} (hn2 : n ≠ 2) (heven : Even n) :
    primalityPrecheck n = some false := by
  by_cases hlt : n < 2
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.lt_succ_iff.mp hlt) with rfl | rfl
    · rfl
    · exact False.elim ((Nat.not_odd_iff_even.mpr heven) (by decide))
  have hn : ¬n < 2 := hlt
  have hne : ¬n = 2 := by exact hn2
  simp only [primalityPrecheck, hn, ↓reduceIte, hne, heven, ↓reduceIte]

/-- Odd nonsquare inputs at least three are passed to the test-specific body. -/
theorem primalityPrecheck_none_of_odd {n : ℕ} (hn3 : 3 ≤ n) (hodd : Odd n) (hns : ¬IsSquare n) :
    primalityPrecheck n = none := by
  have htwo_lt : 2 < n := lt_of_lt_of_le (by decide) hn3
  have hn2 : ¬n < 2 := Nat.not_lt_of_ge htwo_lt.le
  have hnne : n ≠ 2 := Nat.ne_of_gt htwo_lt
  have hneven : ¬Even n := by exact Nat.not_even_iff_odd.mpr hodd
  have hsq : natIsSquare n = false := natIsSquare_false_of_not_isSquare hns
  simp only [primalityPrecheck, hn2, ↓reduceIte, hnne, hneven, ↓reduceIte, hsq, Bool.false_eq_true,
    ↓reduceIte]

end PseudoPrime.PrimeTest
