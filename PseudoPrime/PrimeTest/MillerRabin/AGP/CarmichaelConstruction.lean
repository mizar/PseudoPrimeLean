/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.CarmichaelNumber
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Finset.Defs
public import Mathlib.Algebra.BigOperators.ModEq
public import PseudoPrime.PrimeTest.MillerRabin.AGP.LocalLegendreCriterion
public import PseudoPrime.NumberTheory.PrimeProducts

/-! # Carmichael numbers from finite prime products

This file records the Korselt criterion for products of distinct primes whose
predecessors divide one common modulus.
-/

@[expose] public section

namespace PseudoPrime.PrimeTest.MillerRabin.AGP

/--
Inputs: `S` is a finite set of distinct natural primes, each `p - 1` divides
`K`, and `K` divides the product of the primes minus one.

Claim: the product of `S` is a Carmichael number, provided `S` has at least two
members.

Content: pairwise distinct primes make the product squarefree and nonprime;
the common divisibility conditions give Korselt's divisibility criterion.

Proof: establish squarefreeness from pairwise coprimality, use two distinct
factors for size and nonprimality, then apply `Nat.isCarmichael_iff_korselt`.

Role: this is the Carmichael-number part of the AGP finite subset-product
construction; the subset theorem must supply `S`, `K`, and the congruence.
-/
theorem isCarmichael_finset_prime_product {S : Finset ℕ} {K : ℕ} (hprime : ∀ p ∈ S, Nat.Prime p)
    (hcard : 2 ≤ S.card) (horder : ∀ p ∈ S, p - 1 ∣ K) (hproductMod : K ∣ (∏ p ∈ S, p) - 1) :
    Nat.IsCarmichael (∏ p ∈ S, p) := by
  let a : ℕ := ∏ p ∈ S, p
  have hpair : Set.Pairwise (S : Set ℕ) (Function.onFun IsRelPrime fun p : ℕ => p) := by
    intro p hp q hq hpq
    exact (Nat.coprime_iff_isRelPrime).mp ((Nat.coprime_primes (hprime p hp) (hprime q hq)).2 hpq)
  have hsq : Squarefree a := by
    dsimp [a]
    apply Finset.squarefree_prod_of_pairwise_isCoprime hpair
    intro p hp
    exact (hprime p hp).squarefree
  have htwo : ∃ p ∈ S, ∃ q ∈ S, p ≠ q := by
    apply Finset.one_lt_card.mp
    exact lt_of_lt_of_le (by decide : 1 < 2) hcard
  obtain ⟨p, hp, q, hq, hpq⟩ := htwo
  have hprodPQ : p * q ≤ a := by
    dsimp [a]
    calc
      p * q = ∏ r ∈ ({p, q} : Finset ℕ), r := by simp [hpq]
      _ ≤ ∏ r ∈ S, r :=
        Finset.prod_le_prod_of_subset_of_one_le
          (by
            intro r hr
            simp only [Finset.mem_insert, Finset.mem_singleton] at hr
            rcases hr with hr | hr
            · rw [hr]
              exact hp
            · rw [hr]
              exact hq)
          (by
            intro r hr hrnot
            exact Nat.le_trans (by decide : 1 ≤ 2) ((hprime r hr).two_le))
  have htwoa : 2 < a := by
    dsimp [a] at hprodPQ ⊢
    exact
      lt_of_lt_of_le
        (lt_of_lt_of_le (by decide : 2 < 2 * 2)
          (Nat.mul_le_mul (Nat.Prime.two_le (hprime p hp)) (Nat.Prime.two_le (hprime q hq))))
        hprodPQ
  have hnotprime : ¬Nat.Prime a := by
    intro ha
    have hpdiv : p ∣ a := by
      refine ⟨(∏ r ∈ S.erase p, r), ?_⟩
      dsimp [a]
      calc
        ∏ r ∈ S, r = (∏ r ∈ S.erase p, r) * p := (Finset.prod_erase_mul S (fun r : ℕ => r) hp).symm
        _ = p * (∏ r ∈ S.erase p, r) := Nat.mul_comm _ _
    have hqdiv : q ∣ a := by
      refine ⟨(∏ r ∈ S.erase q, r), ?_⟩
      dsimp [a]
      calc
        ∏ r ∈ S, r = (∏ r ∈ S.erase q, r) * q := (Finset.prod_erase_mul S (fun r : ℕ => r) hq).symm
        _ = q * (∏ r ∈ S.erase q, r) := Nat.mul_comm _ _
    have hpa := ha.eq_one_or_self_of_dvd p hpdiv
    have hqa := ha.eq_one_or_self_of_dvd q hqdiv
    have hpne : p ≠ 1 := Nat.ne_of_gt (Nat.Prime.one_lt (hprime p hp))
    have hqne : q ≠ 1 := Nat.ne_of_gt (Nat.Prime.one_lt (hprime q hq))
    rcases hpa with hpa | hpa
    · exact hpne hpa
    · rcases hqa with hqa | hqa
      · exact hqne hqa
      · exact hpq (hpa.trans hqa.symm)
  apply (Nat.isCarmichael_iff_korselt).2
  refine ⟨htwoa, hnotprime, hsq, ?_⟩
  intro r hr hrdvd
  have hrprime : Prime r := (Nat.prime_iff).mp hr
  have hrdvdprod : r ∣ ∏ p ∈ S, p := by simpa only [a] using hrdvd
  obtain ⟨p, hp, hpr⟩ := (Prime.dvd_finsetProd_iff hrprime (fun p : ℕ => p)).mp hrdvdprod
  have hpeq : p = r := by
    rcases (hprime p hp).eq_one_or_self_of_dvd r hpr with h | h
    · exact False.elim ((Nat.ne_of_gt (Nat.Prime.one_lt hr)) h)
    · exact h.symm
  rw [← hpeq]
  exact dvd_trans (horder p hp) hproductMod

open PseudoPrime.NumberTheory.PrimeProducts in
/--
Inputs: a finite set of distinct primes `S`, a coprime pair `k,L`, and
representations `p = d * k + 1` with `d ∣ L`; also the product of `S` is one
modulo `L`.

Claim: the product of `S` is a Carmichael number.

Content: every factor is one modulo `k`, while the given unit product gives
one modulo `L`; coprimality combines these into the Korselt modulus `k * L`.

Proof: combine the two product congruences, convert the result to divisibility,
and apply the existing finite prime-product Korselt theorem.

Role: turns Proposition 1.3's subgroup product into the Carmichael product
used by the strong Miller-Rabin construction.
-/
theorem isCarmichael_finset_prime_product_of_progression_unit_product {S : Finset ℕ} (L k : ℕ)
    (hkL : Nat.Coprime k L) (hprime : ∀ p ∈ S, Nat.Prime p) (hcard : 2 ≤ S.card)
    (hprogression : ∀ p ∈ S, ∃ d, d ∣ L ∧ p = d * k + 1) (hproductL : (∏ p ∈ S, (p : ZMod L)) = 1) :
    Nat.IsCarmichael (∏ p ∈ S, p) ∧ (∀ p ∈ S, p - 1 ∣ k * L) ∧ k * L ∣ (∏ p ∈ S, p) - 1 := by
  have hmodK : (∏ p ∈ S, p) ≡ 1 [MOD k] := by
    exact
      Nat.ModEq.prod_one fun p hp => by
        obtain ⟨d, hd, hform⟩ := hprogression p hp
        have hpone : 1 ≤ p := by
          rw [hform]
          exact Nat.le_add_left 1 (d * k)
        have hkdvd : k ∣ p - 1 := by
          rw [hform, Nat.add_sub_cancel]
          exact ⟨d, by ac_rfl⟩
        exact ((Nat.modEq_iff_dvd' hpone).2 hkdvd).symm
  have hcastprod : ((∏ p ∈ S, p : ℕ) : ZMod L) = 1 := by
    calc
      _ = ∏ p ∈ S, (p : ZMod L) := map_prod (Nat.castRingHom (ZMod L)) (fun p : ℕ => p) S
      _ = 1 := hproductL
  have hmodL : (∏ p ∈ S, p) ≡ 1 [MOD L] :=
    (ZMod.natCast_eq_natCast_iff (∏ p ∈ S, p) 1 L).mp (hcastprod.trans (Nat.cast_one.symm))
  have hmodKL : (∏ p ∈ S, p) ≡ 1 [MOD k * L] :=
    (Nat.modEq_and_modEq_iff_modEq_mul hkL).mp ⟨hmodK, hmodL⟩
  have hprodge : 1 ≤ ∏ p ∈ S, p :=
    Finset.one_le_prod fun p hp => Nat.le_of_lt (Nat.Prime.one_lt (hprime p hp))
  have hproductMod : k * L ∣ (∏ p ∈ S, p) - 1 := (Nat.modEq_iff_dvd' hprodge).mp hmodKL.symm
  have horder : ∀ p ∈ S, p - 1 ∣ k * L := by
    intro p hp
    obtain ⟨d, hd, hform⟩ := hprogression p hp
    exact predecessor_dvd_mul_of_eq_mul_add_one hform hd
  exact ⟨isCarmichael_finset_prime_product hprime hcard horder hproductMod, horder, hproductMod⟩

open PseudoPrime.NumberTheory.PrimeProducts in
/--
Inputs: the prime and divisibility conditions for a Carmichael product, and a
common Legendre sign for each positive base across all selected primes.

Claim: every base in `W` passes the strong Miller–Rabin test modulo the product.

Content: the prime-factor characterization transfers the selected-prime
conditions to the full product; the local sign criterion then proves passage.

Proof: obtain the Carmichael size and squarefreeness facts, transfer each local
hypothesis to a prime divisor, prove the product odd from the residue condition,
and apply the finite-base criterion from P1.

Role: this connects the P2 prime-product construction to the P1 Miller–Rabin
criterion once the common-sign subset has been supplied.
-/
theorem strongMillerRabinPass_all_of_finset_prime_product {S : Finset ℕ} {K : ℕ} (W : Finset ℕ)
    (hprime : ∀ p ∈ S, Nat.Prime p) (hcard : 2 ≤ S.card) (horder : ∀ p ∈ S, p - 1 ∣ K)
    (hproductMod : K ∣ (∏ p ∈ S, p) - 1) (hpMod : ∀ p ∈ S, p % 4 = 3) (hbase : ∀ b ∈ W, 0 < b)
    (hbp : ∀ b ∈ W, ∀ p ∈ S, ¬p ∣ b)
    (hcommon :
      ∀ b ∈ W,
        ∃ σ : ℤ, (σ = 1 ∨ σ = -1) ∧ ∀ p ∈ S, ∀ (hp : Nat.Prime p), @legendreSym p ⟨hp⟩ b = σ) :
    ∀ b ∈ W, PrimeTest.StrongMillerRabinPass (∏ p ∈ S, p) (b : ZMod (∏ p ∈ S, p)) := by
  let a : ℕ := ∏ p ∈ S, p
  have hoddProduct := odd_finset_product_of_mod_four_eq_three hpMod
  have hCarm := isCarmichael_finset_prime_product hprime hcard horder hproductMod
  obtain ⟨ha2, _, hsq, _⟩ := (Nat.isCarmichael_iff_korselt.mp hCarm)
  have ha1 : 1 < a := by
    dsimp [a]
    exact lt_trans (by decide : 1 < 2) ha2
  have hzero : a ≠ 0 := by
    intro hz
    exact (Nat.ne_of_gt (lt_trans (by decide : 0 < 2) ha2)) hz
  have hmod' : ∀ r, Nat.Prime r → r ∣ a → r % 4 = 3 := by
    intro r hr hrdvd
    obtain ⟨p, hp, hEq⟩ :=
      exists_eq_of_prime_dvd_finset_prime_product hprime hr (by simpa only [a] using hrdvd)
    rw [← hEq]
    exact hpMod p hp
  have hK' : ∀ r, Nat.Prime r → r ∣ a → r - 1 ∣ a - 1 := by
    intro r hr hrdvd
    obtain ⟨p, hp, hEq⟩ :=
      exists_eq_of_prime_dvd_finset_prime_product hprime hr (by simpa only [a] using hrdvd)
    rw [← hEq]
    exact dvd_trans (horder p hp) (by simpa only [a] using hproductMod)
  have hbp' : ∀ b ∈ W, ∀ r, Nat.Prime r → r ∣ a → ¬r ∣ b := by
    intro b hb r hr hrdvd hrb
    obtain ⟨p, hp, hEq⟩ :=
      exists_eq_of_prime_dvd_finset_prime_product hprime hr (by simpa only [a] using hrdvd)
    rw [← hEq] at hrb
    exact hbp b hb p hp hrb
  have hcommon' :
    ∀ b ∈ W,
      ∃ σ : ℤ, (σ = 1 ∨ σ = -1) ∧ ∀ r, (hr : Nat.Prime r) → r ∣ a → @legendreSym r ⟨hr⟩ b = σ := by
    intro b hb
    obtain ⟨σ, hσ, hleg⟩ := hcommon b hb
    refine ⟨σ, hσ, ?_⟩
    intro r hr hrdvd
    obtain ⟨p, hp, hEq⟩ :=
      exists_eq_of_prime_dvd_finset_prime_product hprime hr (by simpa only [a] using hrdvd)
    subst r
    exact hleg p hp (hprime p hp)
  change ∀ b ∈ W, PrimeTest.StrongMillerRabinPass a (b : ZMod a)
  exact
    strongMillerRabinPass_all_of_common_legendre_sign W ha1 hoddProduct hsq hzero hmod' hK' hbase
      hbp' hcommon'

end PseudoPrime.PrimeTest.MillerRabin.AGP
