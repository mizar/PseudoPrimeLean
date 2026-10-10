/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Data.Nat.Find
public import Mathlib.NumberTheory.PrimeCounting

/-!
# Count-indexed primorials

Define the zero-indexed prime sequence starting at `2` and the product of its first `k` entries.
Record the product recurrence and concrete values through the sixth primorial,
which anchor finite numerical certificates.
-/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- The zero-indexed sequence `2, 3, 5, 7, ...` of all primes. -/
noncomputable def primeByIndex (i : ℕ) : ℕ :=
  Nat.nth Nat.Prime i

/-- The product of the first `k` primes; in particular,
`PseudoPrime.NumberTheory.primePrimorialCount 0 = 1`. -/
noncomputable def primePrimorialCount (k : ℕ) : ℕ :=
  ∏ i ∈ Finset.range k, primeByIndex i

/-- The empty count-indexed primorial is `1`. -/
theorem primePrimorialCount_zero : primePrimorialCount 0 = 1 := by
  simp only [primePrimorialCount, Finset.range_zero, Finset.prod_empty]

/-- Adding one factor multiplies the count-indexed primorial by the next prime. -/
theorem primePrimorialCount_succ (k : ℕ) :
    primePrimorialCount (k + 1) = primePrimorialCount k * primeByIndex k := by
  simp only [primePrimorialCount, Finset.prod_range_succ]

/-- The first prime is `2`. -/
theorem primeByIndex_zero : primeByIndex 0 = 2 :=
  Nat.nth_prime_zero_eq_two

/-- The second prime is `3`. -/
theorem primeByIndex_one : primeByIndex 1 = 3 :=
  Nat.nth_prime_one_eq_three

/-- The third prime is `5`. -/
theorem primeByIndex_two : primeByIndex 2 = 5 :=
  Nat.nth_prime_two_eq_five

/-- The fourth prime is `7`. -/
theorem primeByIndex_three : primeByIndex 3 = 7 :=
  Nat.nth_prime_three_eq_seven

/-- The fifth prime is `11`. -/
theorem primeByIndex_four : primeByIndex 4 = 11 :=
  Nat.nth_prime_four_eq_eleven

/-- The sixth prime is `13`. -/
theorem primeByIndex_five : primeByIndex 5 = 13 := by
  have h13 : Nat.Prime 13 := by decide
  have hcount : Nat.count Nat.Prime 13 = 5 := by decide
  rw [primeByIndex, ← Nat.nth_count h13, hcount]

/-- The product of the first six primes is `30030`. -/
theorem primePrimorialCount_six_eq : primePrimorialCount 6 = 30030 := by
  simp only [primePrimorialCount, Finset.prod_range_succ, Finset.prod_range_zero, primeByIndex_zero,
    primeByIndex_one, primeByIndex_two, primeByIndex_three, primeByIndex_four, primeByIndex_five]
  norm_num only

end PseudoPrime.NumberTheory
