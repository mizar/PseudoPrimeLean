/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeProductCountingBounds

/-! # Finite prime-product criteria with the exact ambient Fermat kernel -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For an odd input n>1 and an odd prime power p^a dividing n with a positive,
prime products below p^a outnumber the exact local kernel if choose(card S,k)
exceeds gcd(p-1,n-1). Then a prime in S rejects n. Keep n-1 in the local power
map and transfer subgroup nonmembership to ambient MR failure without GRH. -/
theorem exists_prime_witness_of_exact_kernel_choose {n p a : ℕ} (hn : 1 < n) (ho : Odd n)
    (hp : p.Prime) (hp2 : p ≠ 2) (ha : 0 < a) (hdiv : p ^ a ∣ n) (S : Finset ℕ) (k B : ℕ)
    (hprime : ∀ r ∈ S, Nat.Prime r) (hbound : ∀ r ∈ S, r ≤ B) (hsize : B ^ k < p ^ a)
    (hcount : (p - 1).gcd (n - 1) < Nat.choose S.card k) :
    ∃ r : ℕ, r.Prime ∧ r ≤ B ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  let : NeZero (p ^ a) := ⟨pow_ne_zero a hp.ne_zero⟩
  apply
    exists_prime_witness_of_local_card_lt_choose
      (powMonoidHom (n - 1) : (ZMod (p ^ a))ˣ →* (ZMod (p ^ a))ˣ).ker S k B hprime hbound hsize
  · rw [card_local_fermat_kernel_prime_pow hn hp hp2 ha hdiv]
    exact hcount
  · exact fun r hr ↦ PrimeTest.strongMillerRabinPass_mem_local_divisor_powerKernel hn ho hdiv hr

/-- For positive a and p^a dividing odd n>1, a natural power budget using the
exact kernel size implies an MR rejecting prime through B. Replace the binomial
condition by the proved prime-product power comparison without evaluating it. -/
theorem exists_prime_witness_of_exact_kernel_power_budget {n p a : ℕ} (hn : 1 < n) (ho : Odd n)
    (hp : p.Prime) (hp2 : p ≠ 2) (ha : 0 < a) (hdiv : p ^ a ∣ n) (S : Finset ℕ) (k B : ℕ)
    (hprime : ∀ r ∈ S, Nat.Prime r) (hbound : ∀ r ∈ S, r ≤ B) (hsize : B ^ k < p ^ a)
    (hcount : (p - 1).gcd (n - 1) * k ^ k < (S.card + 1 - k) ^ k) :
    ∃ r : ℕ, r.Prime ∧ r ≤ B ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  exact
    exists_prime_witness_of_exact_kernel_choose hn ho hp hp2 ha hdiv S k B hprime hbound hsize
      (NumberTheory.card_lt_choose_of_power_budget hcount)

/-- For a positive prime-power divisor p^a of odd n>1, B^k<p^a and
choose(pi(B),k)>gcd(p-1,n-1) bound the least prime MR witness by B.
Use all primes up to B and minimize the constructed rejecting-prime predicate.
This finite criterion has no asymptotic threshold or GRH premise. -/
theorem exists_least_prime_witness_of_exact_kernel_prime_count {n p a : ℕ} (hn : 1 < n) (ho : Odd n)
    (hp : p.Prime) (hp2 : p ≠ 2) (ha : 0 < a) (hdiv : p ^ a ∣ n) (k B : ℕ) (hsize : B ^ k < p ^ a)
    (hcount : (p - 1).gcd (n - 1) < Nat.choose B.primeCounting k) :
    ∃ r : ℕ,
      r.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) ∧
        r ≤ B ∧ ∀ s : ℕ, s.Prime → ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) → r ≤ s := by
  classical
  have hc : (p - 1).gcd (n - 1) < Nat.choose B.primesLE.card k := by
    simpa only [Nat.primesLE_card_eq_primeCounting] using hcount
  obtain ⟨r, hr, hb, hf⟩ :=
    exists_prime_witness_of_exact_kernel_choose hn ho hp hp2 ha hdiv B.primesLE k B
      (fun q hq ↦ (Nat.mem_primesLE.mp hq).2) (fun q hq ↦ (Nat.mem_primesLE.mp hq).1) hsize hc
  have hex : ∃ s : ℕ, s.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) := ⟨r, hr, hf⟩
  exact
    ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2,
      (Nat.find_min' hex ⟨hr, hf⟩).trans hb, fun s hs hfail ↦ Nat.find_min' hex ⟨hs, hfail⟩⟩

/-- For an odd n>1 and a prime divisor p, B^k<p and
choose(pi(B),k)>gcd(p-1,n-1) bound the least prime MR witness by B.
Specialize the exact prime-power criterion to a=1 and derive p odd from n odd.
This is the pointwise finite condition, valid also for squarefree inputs. -/
theorem exists_least_prime_witness_of_prime_divisor_prime_count {n p : ℕ} (hn : 1 < n) (ho : Odd n)
    (hp : p.Prime) (hdiv : p ∣ n) (k B : ℕ) (hsize : B ^ k < p)
    (hcount : (p - 1).gcd (n - 1) < Nat.choose B.primeCounting k) :
    ∃ r : ℕ,
      r.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) ∧
        r ≤ B ∧ ∀ s : ℕ, s.Prime → ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) → r ≤ s := by
  have hp2 : p ≠ 2 := fun he ↦ ho.not_two_dvd_nat (he ▸ hdiv)
  exact
    exists_least_prime_witness_of_exact_kernel_prime_count hn ho hp hp2 (a := 1) (by norm_num only)
      (by simpa only [pow_one] using hdiv) k B (by simpa only [pow_one] using hsize) hcount

end PseudoPrime.PrimeTestBounds.MillerRabin
