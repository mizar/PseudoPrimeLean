/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.PrimeProductSubgroupCounting
public import PseudoPrime.NumberTheory.UnitPowerCardinality
public import PseudoPrime.NumberTheory.ChebyshevPrimeCountLower
public import PseudoPrime.PrimeTest.MillerRabin.LocalFermatKernel
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Unconditional MR witnesses from prime-product counting -/

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

/-- For an odd prime power p^a dividing n>1, the ambient (n-1)-power kernel
has size gcd(p-1,n-1). Coprimality of p and n-1 cancels the p-power factor.
Used to bound the local subgroup by p-1 in unconditional witness counting. -/
theorem card_local_fermat_kernel_prime_pow {n p a : ℕ} (hn : 1 < n) (hp : p.Prime) (hp2 : p ≠ 2)
    (ha : 0 < a) (hdiv : p ^ a ∣ n) :
    Nat.card (powMonoidHom (n - 1) : (ZMod (p ^ a))ˣ →* (ZMod (p ^ a))ˣ).ker =
      (p - 1).gcd (n - 1) := by
  have hcop : p.Coprime (n - 1) :=
    ((Nat.coprime_self_sub_right hn.le).mpr (Nat.coprime_one_right n)).of_dvd_left
      ((dvd_pow_self p ha.ne').trans hdiv)
  rw [PseudoPrime.NumberTheory.card_unitPowerKernel_prime_pow hp hp2 ha]
  exact (hcop.pow_left (a - 1)).gcd_mul_left_cancel (p - 1)

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
  · rw [card_local_fermat_kernel_prime_pow hn hp hp2 ha hdiv]
    exact (Nat.gcd_le_left (n - 1) (Nat.sub_pos_of_lt hp.one_lt)).trans_lt hcount
  · exact fun r hr ↦
      PseudoPrime.PrimeTest.strongMillerRabinPass_mem_local_divisor_powerKernel hn ho hdiv hr

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
      (NumberTheory.card_lt_choose_of_power_budget hcount)

/-- The unconditional prime-product budget gives a log-power bound whenever
B is at most log(n)^(2-epsilon). This pointwise criterion keeps the product-count
hypotheses explicit; it does not assert their eventual validity for all inputs. -/
theorem exists_prime_witness_le_log_power_of_prime_product_budget {n p a : ℕ} (hn : 1 < n)
    (ho : Odd n) (hp : p.Prime) (hp2 : p ≠ 2) (ha : 0 < a) (hdiv : p ^ a ∣ n) (S : Finset ℕ)
    (k B : ℕ) (epsilon : ℝ) (hprime : ∀ r ∈ S, Nat.Prime r) (hbound : ∀ r ∈ S, r ≤ B)
    (hsize : B ^ k < p ^ a) (hcount : (p - 1) * k ^ k < (S.card + 1 - k) ^ k)
    (hB : (B : ℝ) ≤ (Real.log n) ^ (2 - epsilon)) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (Real.log n) ^ (2 - epsilon) ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  obtain ⟨r, hr, hb, hf⟩ :=
    exists_prime_witness_of_prime_pow_power_budget hn ho hp hp2 ha hdiv S k B hprime hbound hsize
      hcount
  exact ⟨r, hr, (Nat.cast_le.mpr hb).trans hB, hf⟩

/-- The elementary Chebyshev lower bound supplies M primes at most B. If
B^k < p^a and (p-1)*k^k < (M+1-k)^k, one of them rejects every ambient odd n>1
divisible by p^a. This analytic sufficient criterion needs neither GRH nor a
finite prime list; quantitative choices of B,M,k remain explicit. -/
theorem exists_prime_witness_of_prime_pow_chebyshev_budget {n p a : ℕ} (hn : 1 < n) (ho : Odd n)
    (hp : p.Prime) (hp2 : p ≠ 2) (ha : 0 < a) (hdiv : p ^ a ∣ n) (B M k : ℕ) (hB : 1 < B)
    (hprimecount :
      (M : ℝ) * Real.log B ≤ (B : ℝ) * Real.log 2 - Real.log (B + 1) - 2 * Real.sqrt B * Real.log B)
    (hsize : B ^ k < p ^ a) (hbudget : (p - 1) * k ^ k < (M + 1 - k) ^ k) :
    ∃ r : ℕ, r.Prime ∧ r ≤ B ∧ ¬PseudoPrime.PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_witness_of_prime_pow_choose hn ho hp hp2 ha hdiv B.primesLE k B
      (fun r hr ↦ (Nat.mem_primesLE.mp hr).2) (fun r hr ↦ (Nat.mem_primesLE.mp hr).1) hsize
  rw [Nat.primesLE_card_eq_primeCounting]
  exact
    (NumberTheory.card_lt_choose_of_power_budget hbudget).trans_le
      (Nat.choose_le_choose k (NumberTheory.le_primeCounting_of_chebyshev_lower hB hprimecount))

/-- Under the elementary Chebyshev and prime-product budgets, the least prime
MR rejecting base is at most B. Minimize the full prime-failure predicate, including
the prime two. This states the unconditional criterion directly for a least witness. -/
theorem exists_least_prime_witness_of_prime_pow_chebyshev_budget {n p a : ℕ} (hn : 1 < n)
    (ho : Odd n) (hp : p.Prime) (hp2 : p ≠ 2) (ha : 0 < a) (hdiv : p ^ a ∣ n) (B M k : ℕ)
    (hB : 1 < B)
    (hprimecount :
      (M : ℝ) * Real.log B ≤ (B : ℝ) * Real.log 2 - Real.log (B + 1) - 2 * Real.sqrt B * Real.log B)
    (hsize : B ^ k < p ^ a) (hbudget : (p - 1) * k ^ k < (M + 1 - k) ^ k) :
    ∃ r : ℕ,
      r.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) ∧
        r ≤ B ∧ ∀ s : ℕ, s.Prime → ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) → r ≤ s := by
  classical
  obtain ⟨r, hr, hb, hf⟩ :=
    exists_prime_witness_of_prime_pow_chebyshev_budget hn ho hp hp2 ha hdiv B M k hB hprimecount
      hsize hbudget
  have hex : ∃ s : ℕ, s.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) := ⟨r, hr, hf⟩
  exact
    ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2,
      (Nat.find_min' hex ⟨hr, hf⟩).trans hb, fun s hs hfail ↦ Nat.find_min' hex ⟨hs, hfail⟩⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
