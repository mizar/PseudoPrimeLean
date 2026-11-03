/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Combinatorics.ChoosePowerBounds
public import PseudoPrime.NumberTheory.PrimeProductSubgroupCounting
public import PseudoPrime.NumberTheory.AmbientFermatKernel
public import PseudoPrime.PrimeTest.MillerRabin.LocalFermatKernel

/-! # Transfer of prime-product bounds to MR witnesses -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- If all ambient MR passes map into a local subgroup H, B^k < q and
choose(card S,k) > card H force a rejecting prime at most B from S.
This transports prime-product counting without GRH or a least-witness monotonicity claim. -/
theorem exists_prime_witness_of_local_card_lt_choose {n q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ)
    (S : Finset ℕ) (k B : ℕ) (hprime : ∀ p ∈ S, Nat.Prime p) (hbound : ∀ p ∈ S, p ≤ B)
    (hsize : B ^ k < q) (hcount : Nat.card H < Nat.choose S.card k)
    (hpass :
      ∀ a : ℕ,
        PseudoPrime.PrimeTest.StrongMillerRabinPass n (a : ZMod n) →
          ∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (a : ZMod q)) :
    ∃ p : ℕ, p.Prime ∧ p ≤ B ∧ ¬PseudoPrime.PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  obtain ⟨p, _, hp, hb, hout⟩ :=
    NumberTheory.exists_prime_outside_of_card_lt_choose H S k B hprime hbound hsize hcount
  exact ⟨p, hp, hb, fun hyes ↦ hout (hpass p hyes)⟩

/-- For an odd n>1 divisible by an odd prime power p^a, let S contain primes
at most B. If B^k < p^a and choose(card S,k) > p-1, an actual prime in S
rejects n. Use the ambient Fermat kernel and its exact cardinality; no GRH is needed. -/
theorem exists_prime_witness_of_prime_pow_choose {n p a : ℕ} (hn : 1 < n) (ho : Odd n)
    (hp : p.Prime) (hp2 : p ≠ 2) (ha : 0 < a) (hdiv : p ^ a ∣ n) (S : Finset ℕ) (k B : ℕ)
    (hprime : ∀ r ∈ S, Nat.Prime r) (hbound : ∀ r ∈ S, r ≤ B) (hsize : B ^ k < p ^ a)
    (hcount : p - 1 < Nat.choose S.card k) :
    ∃ r : ℕ, r.Prime ∧ r ≤ B ∧ ¬PseudoPrime.PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  let : NeZero (p ^ a) := ⟨pow_ne_zero a hp.ne_zero⟩
  apply
    exists_prime_witness_of_local_card_lt_choose
      (powMonoidHom (n - 1) : (ZMod (p ^ a))ˣ →* (ZMod (p ^ a))ˣ).ker S k B hprime hbound hsize
  · rw [NumberTheory.card_local_fermat_kernel_prime_pow hn hp hp2 ha hdiv]
    exact (Nat.gcd_le_left (n - 1) (Nat.sub_pos_of_lt hp.one_lt)).trans_lt hcount
  · exact fun r hr ↦ PseudoPrime.PrimeTest.strongMR_local_divisorKernel hn ho hdiv hr

/-- The power budget (p-1)*k^k < (card S+1-k)^k and B^k < p^a force
an actual MR rejecting prime at most B. This sufficient condition uses only natural
powers, avoiding a large binomial evaluation. No GRH assumption is required. -/
theorem exists_prime_witness_of_prime_pow_power_budget {n p a : ℕ} (hn : 1 < n) (ho : Odd n)
    (hp : p.Prime) (hp2 : p ≠ 2) (ha : 0 < a) (hdiv : p ^ a ∣ n) (S : Finset ℕ) (k B : ℕ)
    (hprime : ∀ r ∈ S, Nat.Prime r) (hbound : ∀ r ∈ S, r ≤ B) (hsize : B ^ k < p ^ a)
    (hcount : (p - 1) * k ^ k < (S.card + 1 - k) ^ k) :
    ∃ r : ℕ, r.Prime ∧ r ≤ B ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  exact
    exists_prime_witness_of_prime_pow_choose hn ho hp hp2 ha hdiv S k B hprime hbound hsize
      (Combinatorics.card_lt_choose_of_power_budget hcount)

end PseudoPrime.PrimeTestBounds.MillerRabin
