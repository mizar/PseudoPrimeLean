/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

import Mathlib.Data.Nat.Fib.Zeckendorf

/-!
# Binary search for the greatest Fibonacci index

The search stores adjacent Fibonacci values. A natural-number fuel bound guarantees termination,
and the result agrees with the greatest index defined in mathlib. This provides an executable
basis for Euclidean iteration bounds.
-/

namespace PseudoPrime.NumberTheory.Fibonacci

/--
A Fibonacci search state with an index and two adjacent values. `index` is the index, `value` is
its Fibonacci value, and `next` is the next value. `Valid` relates the fields and is preserved
by addition, doubling, and binary search.
-/
@[ext]
structure State where
  index : Nat
  value : Nat
  next : Nat

/--
The state invariant asserting that the stored values match the index.
-/
def State.Valid (t : State) : Prop :=
  t.value = Nat.fib t.index ∧ t.next = Nat.fib (t.index + 1)

/--
The initial state at index one.
-/
def State.one : State :=
  ⟨1, 1, 1⟩

/--
The state at index zero, returned when fuel is exhausted or the current value exceeds the input
bound.
-/
def State.zero : State :=
  ⟨0, 0, 1⟩

/--
Add two indices using Fibonacci addition identities.
-/
@[inline]
def State.add : State → State → State
  | ⟨i, fi, fi1⟩, ⟨j, fj, fj1⟩ => ⟨i + j, fi * fj1 + (fi1 - fi) * fj, fi1 * fj1 + fi * fj⟩

/--
Double the index using Fibonacci doubling identities.
-/
@[inline]
def State.double : State → State
  | ⟨i, fi, fi1⟩ => ⟨2 * i, fi * (2 * fi1 - fi), fi * fi + fi1 * fi1⟩

/--
Recursively select the binary digits of the index, with recursion depth at most `fuel`.
-/
def greatestFibBinaryLoop (n : Nat) : Nat → State → State
  | 0, _t => State.zero
  | fuel + 1, t =>
    if _h0 : t.value ≤ n then
      let u := greatestFibBinaryLoop n fuel (State.double t)
      let v := State.add t u
      if _h1 : v.value ≤ n then v else u
    else State.zero

/--
A sufficient recursion depth for binary search on a natural input `n`. The bound is `log2 (2 *
log2 (n + 1) + 3) + 1`, placing the greatest index below `2 ^ fuel`. It uses no real logarithms
or rounding and includes input zero.
-/
def greatestFibBinaryFuel (n : Nat) : Nat :=
  Nat.log2 (2 * Nat.log2 (n + 1) + 3) + 1

/--
Compute the greatest Fibonacci index with value at most `n` by binary search. Adjacent values
allow exponential growth of the index, followed by selection of its binary digits during
recursion unwinding. `greatestFibBinary_spec` identifies the result with `Nat.greatestFib n`.
-/
def greatestFibBinary (n : Nat) : Nat :=
  (greatestFibBinaryLoop n (greatestFibBinaryFuel n) State.one).index

/--
The Fibonacci addition identity expressed using adjacent values only.
-/
theorem fib_add_eq (i j : Nat) :
    Nat.fib (i + j) = Nat.fib i * Nat.fib (j + 1) + (Nat.fib (i + 1) - Nat.fib i) * Nat.fib j := by
  cases i with
  | zero => simp only [zero_add, Nat.fib_zero, zero_mul, Nat.fib_one, tsub_zero, one_mul]
  | succ i =>
    simpa only [add_comm, add_left_comm, Nat.reduceAdd, Nat.fib_add_two_sub_fib_add_one,
      Nat.add_assoc] using (Nat.fib_add i j)

/--
The zero state satisfies the state invariant.
-/
theorem State.zero_valid : State.zero.Valid := by
  simp only [Valid, zero, Nat.fib_zero, zero_add, Nat.fib_one, and_self]

/--
The initial state satisfies the state invariant.
-/
theorem State.one_valid : State.one.Valid := by
  simp only [Valid, one, Nat.fib_one, Nat.reduceAdd, Nat.fib_two, and_self]

/--
Adding two valid states preserves the state invariant.
-/
theorem State.add_valid {t u : State} (ht : t.Valid) (hu : u.Valid) : (State.add t u).Valid := by
  rcases t with ⟨i, fi, fi1⟩
  rcases u with ⟨j, fj, fj1⟩
  replace ht : fi = Nat.fib i ∧ fi1 = Nat.fib (i + 1) := by simpa only [Valid] using ht
  rcases ht with ⟨rfl, rfl⟩
  replace hu : fj = Nat.fib j ∧ fj1 = Nat.fib (j + 1) := by simpa only [Valid] using hu
  rcases hu with ⟨rfl, rfl⟩
  constructor
  · simpa only [add] using (fib_add_eq i j).symm
  · simpa only [add, add_comm, add_assoc] using (Nat.fib_add i j).symm

/--
Doubling a valid state preserves the state invariant.
-/
theorem State.double_valid {t : State} (ht : t.Valid) : (State.double t).Valid := by
  rcases t with ⟨i, fi, fi1⟩
  replace ht : fi = Nat.fib i ∧ fi1 = Nat.fib (i + 1) := by simpa only [Valid] using ht
  rcases ht with ⟨rfl, rfl⟩
  constructor
  · simp only [double, Nat.fib_two_mul]
  · simpa only [double, two_mul, add_assoc, pow_two, add_comm] using
      (Nat.fib_two_mul_add_one i).symm

/--
Bound the growth of Fibonacci values over pairs of steps using natural arithmetic.
-/
theorem two_pow_succ_le_fib_two_mul_add_three (m : Nat) : 2 ^ (m + 1) ≤ Nat.fib (2 * m + 3) := by
  induction m with
  | zero => decide
  | succ m ih =>
    calc
      2 ^ (m + 1 + 1) ≤ 2 * Nat.fib (2 * m + 3) := by
        simpa only [pow_succ, Nat.mul_comm, zero_lt_two, mul_le_mul_iff_right₀] using
          Nat.mul_le_mul_left 2 ih
      _ ≤ Nat.fib (2 * m + 3) + Nat.fib (2 * m + 4) := by
        simpa only [two_mul, add_le_add_iff_left, add_le_add_iff_right] using
          add_le_add_left (Nat.fib_le_fib_succ (n := 2 * m + 3)) (Nat.fib (2 * m + 3))
      _ = Nat.fib (2 * (m + 1) + 3) := by
        have hsucc : 1 + (2 * m + 3) = 2 * m + 4 := by ring
        simpa only [Nat.mul_add, mul_one, add_comm, Nat.add_assoc, hsucc] using
          (Nat.fib_add_two (n := 2 * m + 3)).symm

/--
Given a valid input state and sufficient fuel, the search returns a valid state whose index
brackets the greatest index in an interval of width `t.index`.
-/
theorem greatestFibBinaryLoop_spec (n fuel : Nat) :
    ∀ {t : State},
      t.Valid →
        Nat.greatestFib n < t.index * 2 ^ fuel →
        (greatestFibBinaryLoop n fuel t).Valid ∧
          (greatestFibBinaryLoop n fuel t).index ≤ Nat.greatestFib n ∧
          Nat.greatestFib n < (greatestFibBinaryLoop n fuel t).index + t.index := by
  induction fuel with
  | zero =>
    intro t ht hbound
    refine ⟨State.zero_valid, Nat.zero_le _, ?_⟩
    simpa only [greatestFibBinaryLoop, State.zero, zero_add, Nat.greatestFib_lt, pow_zero,
      mul_one] using hbound
  | succ fuel ih =>
    intro t ht hbound
    by_cases h0 : t.value ≤ n
    · have hu :=
        ih (t := State.double t) (State.double_valid ht)
          (by
            simpa only [State.double, Nat.mul_comm, Nat.mul_assoc, Nat.greatestFib_lt,
              pow_succ] using hbound)
      set u := greatestFibBinaryLoop n fuel (State.double t)
      set v := State.add t u
      have hv_valid : v.Valid := by
        simpa only using State.add_valid ht (by simpa only [u] using hu.1)
      by_cases h1 : v.value ≤ n
      · simpa only [greatestFibBinaryLoop, h0, u, v, ↓reduceDIte, h1, Nat.le_greatestFib,
          Nat.greatestFib_lt] using
          (⟨hv_valid, (Nat.le_greatestFib).2 (by simpa only [hv_valid.1] using h1), by
              simpa only [State.add, State.double, two_mul, add_comm, Nat.greatestFib_lt, add_assoc,
                v, u] using hu.2.2⟩ :
            v.Valid ∧ v.index ≤ Nat.greatestFib n ∧ Nat.greatestFib n < v.index + t.index)
      · simpa only [greatestFibBinaryLoop, h0, u, v, ↓reduceDIte, h1, Nat.le_greatestFib,
          Nat.greatestFib_lt] using
          (⟨by simpa only [u] using hu.1, hu.2.1, by
              simpa only [add_comm, Nat.greatestFib_lt, State.add, u, v] using
                (lt_of_not_ge fun hv_ge =>
                    h1 (by simpa only [hv_valid.1] using (Nat.le_greatestFib).1 hv_ge) :
                  Nat.greatestFib n < v.index)⟩ :
            u.Valid ∧ u.index ≤ Nat.greatestFib n ∧ Nat.greatestFib n < u.index + t.index)
    · simpa only [greatestFibBinaryLoop, h0, ↓reduceDIte, State.zero, zero_le, zero_add,
        Nat.greatestFib_lt, true_and] using
        (⟨State.zero_valid, Nat.zero_le _, by
            simpa only [State.zero, zero_add, Nat.greatestFib_lt] using
              (Nat.greatestFib_lt).2 (by simpa only [ht.1, not_le] using h0)⟩ :
          State.zero.Valid ∧
            State.zero.index ≤ Nat.greatestFib n ∧ Nat.greatestFib n < State.zero.index + t.index)

/--
Bound the greatest Fibonacci index using a natural binary logarithm. The estimate `fib (2 * m +
3) >= 2 ^ (m + 1)` avoids real arithmetic. The bound is shared by search fuel and logarithmic
Euclidean iteration bounds.
-/
theorem greatestFib_lt_log2 (n : ℕ) : Nat.greatestFib n < 2 * Nat.log2 (n + 1) + 3 := by
  apply (Nat.greatestFib_lt).2
  exact
    lt_of_lt_of_le (lt_trans (Nat.lt_succ_self n) Nat.lt_log2_self)
      (by
        simpa only [Nat.succ_eq_add_one] using
          two_pow_succ_le_fib_two_mul_add_three (Nat.log2 (n + 1)))

/--
The fuel bound required to apply the search specification to the initial state.
-/
theorem greatestFibBinaryFuel_bound (n : Nat) :
    Nat.greatestFib n < 2 ^ greatestFibBinaryFuel n := by
  calc
    Nat.greatestFib n < 2 * Nat.log2 (n + 1) + 3 := greatestFib_lt_log2 n
    _ < 2 ^ ((2 * Nat.log2 (n + 1) + 3).log2 + 1) := Nat.lt_log2_self
    _ = 2 ^ greatestFibBinaryFuel n := rfl

/--
For every natural input, binary search agrees with `Nat.greatestFib`. Applying the search
interval bounds at initial index one gives equality. This transfers Euclidean fuel bounds to the
executable index computation.
-/
theorem greatestFibBinary_spec (n : Nat) : greatestFibBinary n = Nat.greatestFib n := by
  have hs :=
    greatestFibBinaryLoop_spec n (greatestFibBinaryFuel n) (t := State.one) State.one_valid
      (by simpa only [State.one, one_mul, Nat.greatestFib_lt] using greatestFibBinaryFuel_bound n)
  apply Nat.le_antisymm
  · simpa only [greatestFibBinary, Nat.le_greatestFib] using hs.2.1
  · exact
      Nat.lt_succ_iff.mp
        (by
          simpa only [greatestFibBinary, State.one, Nat.succ_eq_add_one, Nat.greatestFib_lt] using
            hs.2.2)

end PseudoPrime.NumberTheory.Fibonacci
