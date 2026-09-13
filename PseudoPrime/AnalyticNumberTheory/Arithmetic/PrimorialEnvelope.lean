/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import Mathlib.Data.Nat.Find
import Mathlib.Data.Finset.Sort
import Mathlib.NumberTheory.PrimeCounting
import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimeFactors

/-!
# Odd primorial envelopes

The `k`-th odd prime is the `(k + 1)`-st member of mathlib's zero-indexed sequence of all primes.
Their initial products provide the natural lower envelope for odd integers with many distinct
prime factors.
-/

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- The zero-indexed sequence `3, 5, 7, ...` of odd primes. -/
noncomputable def oddPrime (k : ℕ) : ℕ :=
  Nat.nth Nat.Prime (k + 1)

/-- The product of the first `k` odd primes; in particular,
`PseudoPrime.AnalyticNumberTheory.Arithmetic.oddPrimorial 0 = 1`. -/
noncomputable def oddPrimorial (k : ℕ) : ℕ :=
  ∏ i ∈ Finset.range k, oddPrime i

/-- Every member of `PseudoPrime.AnalyticNumberTheory.Arithmetic.oddPrime` is prime. -/
theorem oddPrime_prime (k : ℕ) : (oddPrime k).Prime :=
  Nat.prime_nth_prime (k + 1)

/-- The odd-prime sequence is strictly increasing. -/
theorem oddPrime_strictMono : StrictMono oddPrime :=
  fun _ _ h => Nat.nth_strictMono Nat.infinite_setOfPred_prime (Nat.add_lt_add_right h 1)

/-- The first odd prime is `3`. -/
theorem oddPrime_zero : oddPrime 0 = 3 := by
  simp only [oddPrime, zero_add,
    Nat.nth_prime_one_eq_three]

/-- Every member of `PseudoPrime.AnalyticNumberTheory.Arithmetic.oddPrime` is at least `3`. -/
theorem three_le_oddPrime (k : ℕ) : 3 ≤ oddPrime k := by
  rw [← oddPrime_zero]
  exact oddPrime_strictMono.monotone (Nat.zero_le k)

/-- Every member of `PseudoPrime.AnalyticNumberTheory.Arithmetic.oddPrime` is odd. -/
theorem oddPrime_odd (k : ℕ) : Odd (oddPrime k) := by
  apply (oddPrime_prime k).odd_of_ne_two
  exact
    ne_of_gt
      ((by norm_num only : 2 < 3).trans_le
        (three_le_oddPrime k))

/-- The empty odd primorial is `1`. -/
theorem oddPrimorial_zero : oddPrimorial 0 = 1 := by
  simp only [oddPrimorial, Finset.range_zero,
    Finset.prod_empty]

/-- Adding one factor multiplies the odd primorial by the next odd prime. -/
theorem oddPrimorial_succ (k : ℕ) :
    oddPrimorial (k + 1) =
      oddPrimorial k *
        oddPrime k := by
  simp only [oddPrimorial, Finset.prod_range_succ]

/-- Every odd primorial is positive. -/
theorem oddPrimorial_pos (k : ℕ) :
    0 < oddPrimorial k := by
  induction k with
  | zero =>
    rw [oddPrimorial_zero]; norm_num only
  | succ k hk =>
    rw [oddPrimorial_succ]
    exact Nat.mul_pos hk (oddPrime_prime k).pos

/-- Odd primorials are monotone in the number of factors. -/
theorem oddPrimorial_monotone :
    Monotone oddPrimorial := by
  apply monotone_nat_of_le_succ
  intro k
  rw [oddPrimorial_succ]
  have hpos := oddPrimorial_pos k
  have hprime := three_le_oddPrime k
  nlinarith only [hpos, hprime]

/-- The `i`-th odd prime is at most the `i`-th member of any finite set of odd primes. -/
theorem oddPrime_le_orderEmbOfFin {s : Finset ℕ} (hprime : ∀ p ∈ s, p.Prime) (hodd : ∀ p ∈ s, Odd p)
    (i : Fin s.card) :
    oddPrime i ≤ s.orderEmbOfFin rfl i := by
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
        rcases htwo with ⟨k, hk⟩
        omega
      omega
    | succ j ih =>
      intro hj
      have hj' : j < s.card := (Nat.lt_succ_self j).trans hj
      have hlt : Nat.count Nat.Prime (f ⟨j, hj'⟩) < Nat.count Nat.Prime (f ⟨j + 1, hj⟩) :=
        Nat.count_strict_mono (hfprime ⟨j, hj'⟩) (f.strictMono (by exact Nat.lt_succ_self j))
      have hind := ih hj'
      omega
  rw [oddPrime, ← Nat.nth_count (hfprime i)]
  exact Nat.nth_monotone Nat.infinite_setOfPred_prime (hcountNat i.val i.isLt)

/-- The product of any finite set of odd primes dominates the matching odd primorial. -/
theorem oddPrimorial_card_le_prod {s : Finset ℕ} (hprime : ∀ p ∈ s, p.Prime)
    (hodd : ∀ p ∈ s, Odd p) :
    oddPrimorial s.card ≤ ∏ p ∈ s, p := by
  rw [oddPrimorial, ← Fin.prod_univ_eq_prod_range]
  calc
    ∏ i : Fin s.card, oddPrime i ≤
        ∏ i : Fin s.card, s.orderEmbOfFin rfl i :=
      Finset.prod_le_prod fun i _ =>
        oddPrime_le_orderEmbOfFin hprime hodd i
    _ = ∏ p : s, (p : ℕ) := Equiv.prod_comp (s.orderIsoOfFin rfl).toEquiv fun p : s => (p : ℕ)
    _ = ∏ p ∈ s, p := by simpa only [id_eq] using (Finset.prod_coe_sort s id)

/-- An odd natural number dominates the odd primorial indexed by its distinct prime factors. -/
theorem oddPrimorial_le_of_card_primeFactors {n : ℕ} (hn : Odd n) :
    oddPrimorial n.primeFactors.card ≤ n := by
  have hodd : ∀ p ∈ n.primeFactors, Odd p := fun _ hp =>
    hn.of_dvd_nat (Nat.mem_primeFactors.mp hp).2.1
  have hprod :=
    oddPrimorial_card_le_prod
      (fun _ hp => (Nat.mem_primeFactors.mp hp).1) hodd
  exact hprod.trans (Nat.le_of_dvd hn.pos (Nat.prod_primeFactors_dvd n))

/-- An odd primorial exceeding `n` gives a strict upper bound on its number of prime factors. -/
theorem distinctPrimeFactorCount_lt_of_lt_oddPrimorial {n k : ℕ} (hn : Odd n)
    (hnk : n < oddPrimorial k) :
    distinctPrimeFactorCount n < k := by
  rw [distinctPrimeFactorCount,
    ArithmeticFunction.cardDistinctFactors_apply, ← List.card_toFinset]
  by_contra hnot
  have hk : k ≤ n.primeFactors.card := Nat.le_of_not_gt hnot
  exact
    not_lt_of_ge
      (oddPrimorial_monotone hk |>.trans
        (oddPrimorial_le_of_card_primeFactors hn))
      hnk

/-- A bounded odd input inherits a non-strict factor-count bound from the next primorial. -/
theorem distinctPrimeFactorCount_le_of_le_of_lt_oddPrimorial_succ {n B k : ℕ} (hn : Odd n)
    (hnB : n ≤ B) (hB : B < oddPrimorial (k + 1)) :
    distinctPrimeFactorCount n ≤ k := by
  have hlt :=
    distinctPrimeFactorCount_lt_of_lt_oddPrimorial hn
      (hnB.trans_lt hB)
  omega

/-- The index of an odd primorial never exceeds the product itself. -/
theorem le_oddPrimorial (k : ℕ) :
    k ≤ oddPrimorial k := by
  induction k with
  | zero => exact Nat.zero_le _
  | succ k hk =>
    rw [oddPrimorial_succ]
    have hpos := oddPrimorial_pos k
    have hprime := three_le_oddPrime k
    nlinarith only [hk, hpos, hprime, Nat.le_mul_of_pos_right k hpos]

/-- The largest `k ≤ B` for which the first `k` odd primes have product at most `B`. -/
noncomputable def maxOddPrimeFactorCount (B : ℕ) : ℕ := by
  classical
    exact
    Nat.findGreatest (fun k => oddPrimorial k ≤ B) B

/-- Any odd primorial bounded by `B` has index at most
`PseudoPrime.AnalyticNumberTheory.Arithmetic.maxOddPrimeFactorCount B`. -/
theorem le_maxOddPrimeFactorCount {B k : ℕ}
    (hk : oddPrimorial k ≤ B) :
    k ≤ maxOddPrimeFactorCount B := by
  classical
  unfold maxOddPrimeFactorCount
  exact
    Nat.le_findGreatest (P := fun i =>
      oddPrimorial i ≤ B)
      (le_oddPrimorial k |>.trans hk) hk

end PseudoPrime.AnalyticNumberTheory.Arithmetic
