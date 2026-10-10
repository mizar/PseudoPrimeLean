/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Algebra.Group.Even
public import Mathlib.Data.Nat.Sqrt
public import PseudoPrime.PrimeTest.Basic

/-!
# Common small-input, parity, and square precheck

The precheck handles the values below `3`, all even values, and square values.
Odd nonsquare inputs at least `3` are left to the test-specific executable body.
-/

@[expose] public section

namespace PseudoPrime.PrimeTest

/--
Executable square test for a natural input `n`.
Compare `Nat.sqrt n ^ 2` with `n` using Boolean equality. The result is a Boolean, not the
optional classification returned by `primalityPrecheck`. The precheck uses it after handling
small inputs and parity to reject square candidates before a test-specific computation.
-/
def natIsSquare (n : ℕ) : Bool :=
  Nat.sqrt n ^ 2 == n

/--
A nonsquare natural input is rejected by the executable square comparison.
From `¬IsSquare n`, conclude `natIsSquare n = false`. If the comparison were true,
`Nat.sqrt n` would witness `IsSquare n`, contradicting the premise. This supplies the square
branch needed to show that odd nonsquares pass through the primality precheck.
-/
theorem natIsSquare_false_of_not_isSquare {n : ℕ} (hns : ¬IsSquare n) : natIsSquare n = false := by
  by_contra h
  apply hns
  apply (isSquare_iff_exists_sq n).mpr
  refine ⟨Nat.sqrt n, ?_⟩
  have htrue : natIsSquare n = true := Bool.eq_true_of_not_eq_false h
  simpa only [natIsSquare] using (beq_iff_eq.mp htrue).symm

/--
Optional classification before running a test-specific primality filter.
For any natural `n`, return `some false` below `2`, `some true` at `2`, and `some false` for
other even inputs or squares; return `none` for the remaining odd nonsquares.
`none` delegates to the caller's test and does not denote a negative conclusion.
The branch order ensures that the prime `2` is accepted before parity rejection.
-/
def primalityPrecheck (n : ℕ) : Option Bool :=
  if n < 2 then some false
  else
    if n = 2 then some true
    else if Even n then some false else if natIsSquare n then some false else none

/--
The precheck classifies `0` as rejected: `primalityPrecheck 0 = some false`.
There are no premises. The first small-input branch reduces definitionally, so the proof is
reflexivity. This fixes the lower boundary of top-level primality-test contracts.
-/
theorem primalityPrecheck_zero : primalityPrecheck 0 = some false := by rfl

/--
The precheck classifies `1` as rejected: `primalityPrecheck 1 = some false`.
There are no premises; the first small-input branch computes the result by reflexivity.
Top-level contracts reuse this boundary classification to exclude the unit input.
-/
theorem primalityPrecheck_one : primalityPrecheck 1 = some false := by rfl

/--
The precheck accepts `2` before applying the even-input rejection branch.
There are no premises, and the defining branches reduce to `some true` by reflexivity.
This supplies the distinguished even-prime case in top-level correctness contracts.
-/
theorem primalityPrecheck_two : primalityPrecheck 2 = some true := by rfl

/--
Every even natural input other than `2` is classified as rejected.
The premises are `n ≠ 2` and `Even n`; the conclusion is `primalityPrecheck n = some false`.
The proof separates inputs below `2`, then simplifies the explicit parity branch for the rest.
Top-level primality filters use this result independently of their arithmetic test body.
-/
theorem primalityPrecheck_even_false {n : ℕ} (hn2 : n ≠ 2) (heven : Even n) :
    primalityPrecheck n = some false := by
  by_cases hlt : n < 2
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.lt_succ_iff.mp hlt) with rfl | rfl
    · rfl
    · exact False.elim ((Nat.not_odd_iff_even.mpr heven) (by decide))
  have hn : ¬n < 2 := hlt
  have hne : ¬n = 2 := by exact hn2
  simp only [primalityPrecheck, hn, ↓reduceIte, hne, heven, ↓reduceIte]

/--
Odd nonsquares at least `3` reach the test-specific body.
From `3 ≤ n`, `Odd n`, and `¬IsSquare n`, conclude `primalityPrecheck n = none`.
The proof excludes the small-input, equality-to-two, even, and square branches explicitly.
This is the interface used to unfold top-level tests on their intended arithmetic domain.
-/
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
