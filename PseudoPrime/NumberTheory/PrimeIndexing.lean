/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import Mathlib.Data.Nat.Find
import Mathlib.Data.Finset.Sort
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Tactic.Linarith

/-!
# Count-indexed primorials

This file records the product of the first `k` primes (all primes, zero-indexed from `2`), and
proves that the product of any finite set of `k` primes is at least this product.
Ordering the finite set compares each entry with the prime of the same index.
It also records the concrete values of the first few primes in this indexing
and the resulting sixth count-indexed primorial, used to anchor finite numeric certificates.
-/

namespace PseudoPrime.NumberTheory

/-- The zero-indexed sequence `2, 3, 5, 7, ...` of all primes. -/
noncomputable def primeByIndex (i : ℕ) : ℕ :=
  Nat.nth Nat.Prime i

/-- The product of the first `k` primes; in particular,
`PseudoPrime.NumberTheory.primePrimorialCount 0 = 1`. -/
noncomputable def primePrimorialCount (k : ℕ) : ℕ :=
  ∏ i ∈ Finset.range k, primeByIndex i

/-- Every member of `PseudoPrime.NumberTheory.primeByIndex` is prime. -/
theorem primeByIndex_prime (i : ℕ) : (primeByIndex i).Prime :=
  Nat.prime_nth_prime i

/-- The empty count-indexed primorial is `1`. -/
theorem primePrimorialCount_zero : primePrimorialCount 0 = 1 := by
  simp only [primePrimorialCount, Finset.range_zero, Finset.prod_empty]

/-- Adding one factor multiplies the count-indexed primorial by the next prime. -/
theorem primePrimorialCount_succ (k : ℕ) :
    primePrimorialCount (k + 1) =
      primePrimorialCount k * primeByIndex k := by
  simp only [primePrimorialCount, Finset.prod_range_succ]

/-- Every count-indexed primorial is positive. -/
theorem primePrimorialCount_pos (k : ℕ) : 0 < primePrimorialCount k := by
  induction k with
  | zero =>
    rw [primePrimorialCount_zero]; norm_num only
  | succ k hk =>
    rw [primePrimorialCount_succ]
    exact Nat.mul_pos hk (primeByIndex_prime k).pos

/-- The `i`-th prime is at most the `i`-th member of any finite set of primes. -/
theorem primeByIndex_le_orderEmbOfFin {s : Finset ℕ} (hprime : ∀ p ∈ s, p.Prime) (i : Fin s.card) :
    primeByIndex i ≤ s.orderEmbOfFin rfl i := by
  let f := s.orderEmbOfFin rfl
  have hfprime (j : Fin s.card) : (f j).Prime := hprime _ (s.orderEmbOfFin_mem rfl j)
  have hcountNat : ∀ j, ∀ hj : j < s.card, j ≤ Nat.count Nat.Prime (f ⟨j, hj⟩) := by
    intro j
    induction j with
    | zero =>
      intro hj; exact Nat.zero_le _
    | succ j ih =>
      intro hj
      have hj' : j < s.card := (Nat.lt_succ_self j).trans hj
      have hlt : Nat.count Nat.Prime (f ⟨j, hj'⟩) < Nat.count Nat.Prime (f ⟨j + 1, hj⟩) :=
        Nat.count_strict_mono (hfprime ⟨j, hj'⟩) (f.strictMono (by exact Nat.lt_succ_self j))
      have hind := ih hj'
      omega
  rw [primeByIndex, ← Nat.nth_count (hfprime i)]
  exact Nat.nth_monotone Nat.infinite_setOfPred_prime (hcountNat i.val i.isLt)

/-- The product of any finite set of primes dominates the matching count-indexed primorial. -/
theorem primePrimorialCount_card_le_prod {s : Finset ℕ} (hprime : ∀ p ∈ s, p.Prime) :
    primePrimorialCount s.card ≤ ∏ p ∈ s, p := by
  rw [primePrimorialCount, ← Fin.prod_univ_eq_prod_range]
  calc
    ∏ i : Fin s.card, primeByIndex i ≤
        ∏ i : Fin s.card, s.orderEmbOfFin rfl i :=
      Finset.prod_le_prod fun i _ => primeByIndex_le_orderEmbOfFin hprime i
    _ = ∏ p : s, (p : ℕ) := Equiv.prod_comp (s.orderIsoOfFin rfl).toEquiv fun p : s => (p : ℕ)
    _ = ∏ p ∈ s, p := by simpa only [id_eq] using (Finset.prod_coe_sort s id)

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
  simp only [primePrimorialCount, Finset.prod_range_succ,
    Finset.prod_range_zero, primeByIndex_zero,
    primeByIndex_one, primeByIndex_two,
    primeByIndex_three, primeByIndex_four,
    primeByIndex_five]
  norm_num only

end PseudoPrime.NumberTheory
