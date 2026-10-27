/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Finset.Max

/-! # A small paired prime-factor modulus

Four distinct prime factors permit a product modulus no larger than sqrt(n).
-/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- A positive integer with at least four distinct prime factors admits two
distinct prime factors whose product has square at most n. Select the least
two factors and two remaining factors; the four-factor product divides n.
This controls the modulus in the paired-character local MR branch. -/
theorem exists_primeFactors_pair_square_le {n : ℕ} (hn : 0 < n) (hc : 4 ≤ n.primeFactors.card) :
    ∃ p ∈ n.primeFactors, ∃ q ∈ n.primeFactors, p ≠ q ∧ (p * q) ^ 2 ≤ n := by
  let S := n.primeFactors
  have hS : S.Nonempty := Finset.card_pos.mp ((by decide : 0 < 4).trans_le hc)
  let p := S.min' hS
  have hp : p ∈ S := Finset.min'_mem S hS
  have hTcard : 3 ≤ (S.erase p).card := by
    rw [Finset.card_erase_of_mem hp]
    exact Nat.sub_le_sub_right hc 1
  have hT : (S.erase p).Nonempty := Finset.card_pos.mp ((by decide : 0 < 3).trans_le hTcard)
  let q := (S.erase p).min' hT
  have hq := Finset.min'_mem (S.erase p) hT
  have hUcard : 2 ≤ ((S.erase p).erase q).card := by
    rw [Finset.card_erase_of_mem hq]
    exact Nat.sub_le_sub_right hTcard 1
  obtain ⟨r, hr, s, hs, hrs⟩ := Finset.one_lt_card.mp ((by decide : 1 < 2).trans_le hUcard)
  have hrT := (Finset.mem_erase.mp hr).2
  have hsT := (Finset.mem_erase.mp hs).2
  have hrS := (Finset.mem_erase.mp hrT).2
  have hsS := (Finset.mem_erase.mp hsT).2
  have hqS := (Finset.mem_erase.mp hq).2
  have hpq : p ≠ q := (Finset.mem_erase.mp hq).1.symm
  have hpr : p ≠ r := (Finset.mem_erase.mp hrT).1.symm
  have hps : p ≠ s := (Finset.mem_erase.mp hsT).1.symm
  have hqr : q ≠ r := (Finset.mem_erase.mp hr).1.symm
  have hqs : q ≠ s := (Finset.mem_erase.mp hs).1.symm
  have hsub : ({p, q, r, s} : Finset ℕ) ⊆ S := by
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨hp, hqS, hrS, hsS⟩
  have hprod :=
    (Finset.prod_dvd_prod_of_subset _ _ (fun x : ℕ ↦ x) hsub).trans (Nat.prod_primeFactors_dvd n)
  have hfour : p * q * r * s ∣ n := by
    simpa only [Finset.prod_insert, Finset.prod_singleton, Finset.mem_insert, Finset.mem_singleton,
      hpq, hpr, hps, hqr, hqs, hrs, or_self, not_false_eq_true, mul_assoc] using hprod
  have hpR : p ≤ r := Finset.min'_le S r hrS
  have hqSle : q ≤ s := Finset.min'_le (S.erase p) s hsT
  refine ⟨p, hp, q, hqS, hpq, ?_⟩
  calc
    (p * q) ^ 2 = (p * q) * (p * q) := pow_two _
    _ ≤ (p * q) * (r * s) := Nat.mul_le_mul_left _ (Nat.mul_le_mul hpR hqSle)
    _ = p * q * r * s := (mul_assoc _ _ _).symm
    _ ≤ n := Nat.le_of_dvd hn hfour

/-- For positive n with at least four distinct prime factors, select distinct
primes p,q whose product divides n and has square at most n. Convert the
prime-factor membership witnesses and combine their coprime divisors.
This supplies the local modulus and size hypotheses for MR witness transfer. -/
theorem exists_prime_pair_modulus_square_le {n : ℕ} (hn : 0 < n) (hc : 4 ≤ n.primeFactors.card) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p * q ∣ n ∧ (p * q) ^ 2 ≤ n := by
  obtain ⟨p, hp, q, hq, hpq, hs⟩ := exists_primeFactors_pair_square_le hn hc
  have hpF := Nat.mem_primeFactors.mp hp
  have hqF := Nat.mem_primeFactors.mp hq
  have hcop := (Nat.coprime_primes hpF.1 hqF.1).mpr hpq
  exact ⟨p, q, hpF.1, hqF.1, hpq, hcop.mul_dvd_of_dvd_of_dvd hpF.2.1 hqF.2.1, hs⟩

end PseudoPrime.NumberTheory
