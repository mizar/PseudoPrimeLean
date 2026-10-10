/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Data.Nat.Find
public import Mathlib.Data.Finset.Sort
public import Mathlib.NumberTheory.PrimeCounting
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimeFactors

/-!
# Odd primorial envelopes

The `k`-th odd prime is the `(k + 1)`-st member of mathlib's zero-indexed sequence of all primes.
Their initial products provide the natural lower envelope for odd integers with many distinct
prime factors.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- For natural `k`, the prime at index `k + 1` in mathlib's zero-indexed prime sequence,
giving `3, 5, 7, ...`. Skipping the initial two defines the odd factors in primorial envelopes. -/
noncomputable def oddPrime (k : ℕ) : ℕ :=
  Nat.nth Nat.Prime (k + 1)

/-- The product of the first `k` odd primes; in particular,
`PseudoPrime.AnalyticNumberTheory.Arithmetic.oddPrimorial 0 = 1`. -/
noncomputable def oddPrimorial (k : ℕ) : ℕ :=
  ∏ i ∈ Finset.range k, oddPrime i

/-- For every natural `k`, `oddPrime k` is prime by the primality theorem for `Nat.nth`.
This supplies primality of each factor in the odd primorial. -/
theorem oddPrime_prime (k : ℕ) : (oddPrime k).Prime :=
  Nat.prime_nth_prime (k + 1)

/-- The sequence `oddPrime` is strictly increasing. Infinitude of the primes makes their
`Nat.nth` enumeration strictly increasing, and the index shift preserves order.
This compares odd prime indices with sorted prime supports. -/
theorem oddPrime_strictMono : StrictMono oddPrime := fun _ _ h =>
  Nat.nth_strictMono Nat.infinite_setOfPred_prime (Nat.add_lt_add_right h 1)

/-- The zero-indexed first odd prime is three, by mathlib's value for prime index one.
This initializes the lower bounds for all odd primes. -/
theorem oddPrime_zero : oddPrime 0 = 3 := by
  simp only [oddPrime, zero_add, Nat.nth_prime_one_eq_three]

/-- For every natural `k`, `3 ≤ oddPrime k`. Compare index zero with `k` using monotonicity
and the value `oddPrime 0 = 3`. This excludes two and bounds each primorial factor below. -/
theorem three_le_oddPrime (k : ℕ) : 3 ≤ oddPrime k := by
  rw [← oddPrime_zero]
  exact oddPrime_strictMono.monotone (Nat.zero_le k)

/-- Every `oddPrime k` is odd: it is prime and at least three, hence differs from two.
This verifies that the enumeration belongs to the odd-prime supports being compared. -/
theorem oddPrime_odd (k : ℕ) : Odd (oddPrime k) := by
  apply (oddPrime_prime k).odd_of_ne_two
  exact ne_of_gt ((by norm_num only : 2 < 3).trans_le (three_le_oddPrime k))

/-- The product of the first zero odd primes is one, by the empty-product convention.
This is the base case for inductive odd-primorial estimates. -/
theorem oddPrimorial_zero : oddPrimorial 0 = 1 := by
  simp only [oddPrimorial, Finset.range_zero, Finset.prod_empty]

/-- For natural `k`, `oddPrimorial (k + 1) = oddPrimorial k * oddPrime k`.
The finite-range product recurrence isolates the next factor and supports induction on
the number of distinct odd primes. -/
theorem oddPrimorial_succ (k : ℕ) : oddPrimorial (k + 1) = oddPrimorial k * oddPrime k := by
  simp only [oddPrimorial, Finset.prod_range_succ]

/-- In any finite set `s` of odd primes, its increasingly ordered entry at index
`i : Fin s.card` is at least `oddPrime i`. Induction on the index shows that each entry
has at least `i + 1` primes below it, accounting for two as well; monotonicity of `Nat.nth`
gives the bound. This is the termwise input for the primorial product comparison. -/
theorem oddPrime_le_orderEmbOfFin {s : Finset ℕ} (hprime : ∀ p ∈ s, p.Prime) (hodd : ∀ p ∈ s, Odd p)
    (i : Fin s.card) : oddPrime i ≤ s.orderEmbOfFin rfl i := by
  let f := s.orderEmbOfFin rfl
  have hfprime (j : Fin s.card) : (f j).Prime := hprime _ (s.orderEmbOfFin_mem rfl j)
  have hfodd (j : Fin s.card) : Odd (f j) := hodd _ (s.orderEmbOfFin_mem rfl j)
  have hcountNat : ∀ j, ∀ hj : j < s.card, j + 1 ≤ Nat.count Nat.Prime (f ⟨j, hj⟩) := by
    intro j
    induction j with
    | zero =>
      intro hj
      have hne : Nat.count Nat.Prime (f ⟨0, hj⟩) ≠ 0 := by
        intro hz
        have heq := Nat.nth_count (hfprime ⟨0, hj⟩)
        rw [hz, Nat.nth_prime_zero_eq_two] at heq
        have htwo : Odd 2 := heq.symm ▸ hfodd ⟨0, hj⟩
        exact (Nat.not_odd_iff_even.mpr ⟨1, rfl⟩) htwo
      exact Nat.one_le_iff_ne_zero.mpr hne
    | succ j ih =>
      intro hj
      have hj' : j < s.card := (Nat.lt_succ_self j).trans hj
      have hlt : Nat.count Nat.Prime (f ⟨j, hj'⟩) < Nat.count Nat.Prime (f ⟨j + 1, hj⟩) :=
        Nat.count_strict_mono (hfprime ⟨j, hj'⟩) (f.strictMono (by exact Nat.lt_succ_self j))
      have hind := ih hj'
      exact Nat.succ_le_iff.mpr (lt_of_le_of_lt hind hlt)
  rw [oddPrime, ← Nat.nth_count (hfprime i)]
  exact Nat.nth_monotone Nat.infinite_setOfPred_prime (hcountNat i.val i.isLt)

/-- If every member of a finite set `s` is an odd prime, then `oddPrimorial s.card` is
at most its product. Sort the set, compare each factor with the corresponding odd prime,
and reindex the product through the order isomorphism. This bounds the product of an odd
integer's distinct prime factors from below. -/
theorem oddPrimorial_card_le_prod {s : Finset ℕ} (hprime : ∀ p ∈ s, p.Prime)
    (hodd : ∀ p ∈ s, Odd p) : oddPrimorial s.card ≤ ∏ p ∈ s, p := by
  rw [oddPrimorial, ← Fin.prod_univ_eq_prod_range]
  calc
    ∏ i : Fin s.card, oddPrime i ≤ ∏ i : Fin s.card, s.orderEmbOfFin rfl i :=
      Finset.prod_le_prod fun i _ => oddPrime_le_orderEmbOfFin hprime hodd i
    _ = ∏ p : s, (p : ℕ) := Equiv.prod_comp (s.orderIsoOfFin rfl).toEquiv fun p : s => (p : ℕ)
    _ = ∏ p ∈ s, p := by simpa only [id_eq] using (Finset.prod_coe_sort s id)

/-- For odd natural `n`, `oddPrimorial n.primeFactors.card ≤ n`.
Its prime factors are odd, their product dominates the corresponding odd primorial, and
that product divides the positive `n`. This is the lower envelope for factor-count estimates. -/
theorem oddPrimorial_le_of_card_primeFactors {n : ℕ} (hn : Odd n) :
    oddPrimorial n.primeFactors.card ≤ n := by
  have hodd : ∀ p ∈ n.primeFactors, Odd p := fun _ hp =>
    hn.of_dvd_nat (Nat.mem_primeFactors.mp hp).2.1
  have hprod := oddPrimorial_card_le_prod (fun _ hp => (Nat.mem_primeFactors.mp hp).1) hodd
  exact hprod.trans (Nat.le_of_dvd hn.pos (Nat.prod_primeFactors_dvd n))

end PseudoPrime.AnalyticNumberTheory.Arithmetic
