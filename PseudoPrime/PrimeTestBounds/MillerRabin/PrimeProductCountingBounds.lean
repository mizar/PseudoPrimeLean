/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeProductCountingTransfer
public import PseudoPrime.NumberTheory.ChebyshevPrimeCountLower
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Analytic MR witness criteria from prime-product bounds -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The unconditional prime-product budget gives a log-power bound whenever
B is at most log(n)^(2-epsilon). This pointwise criterion keeps the product-count
hypotheses explicit; it does not assert their eventual validity for all inputs. -/
theorem exists_prime_logPower_productBudget {n p a : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hp2 : p ≠ 2) (ha : 0 < a) (hdiv : p ^ a ∣ n) (S : Finset ℕ) (k B : ℕ) (epsilon : ℝ)
    (hprime : ∀ r ∈ S, Nat.Prime r) (hbound : ∀ r ∈ S, r ≤ B) (hsize : B ^ k < p ^ a)
    (hcount : (p - 1) * k ^ k < (S.card + 1 - k) ^ k)
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
theorem exists_prime_primePow_chebyshevBudget {n p a : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hp2 : p ≠ 2) (ha : 0 < a) (hdiv : p ^ a ∣ n) (B M k : ℕ) (hB : 1 < B)
    (hprimecount :
      (M : ℝ) * Real.log B ≤ (B : ℝ) * Real.log 2 - Real.log (B + 1) - 2 * Real.sqrt B * Real.log B)
    (hsize : B ^ k < p ^ a) (hbudget : (p - 1) * k ^ k < (M + 1 - k) ^ k) :
    ∃ r : ℕ, r.Prime ∧ r ≤ B ∧ ¬PseudoPrime.PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    exists_prime_witness_of_prime_pow_choose hn ho hp hp2 ha hdiv B.primesLE k B
      (fun r hr ↦ (Nat.mem_primesLE.mp hr).2) (fun r hr ↦ (Nat.mem_primesLE.mp hr).1) hsize
  rw [Nat.primesLE_card_eq_primeCounting]
  exact
    (Combinatorics.card_lt_choose_of_power_budget hbudget).trans_le
      (Nat.choose_le_choose k (NumberTheory.le_primeCounting_of_chebyshev_lower hB hprimecount))

/-- Under the elementary Chebyshev and prime-product budgets, the least prime
MR rejecting base is at most B. Minimize the full prime-failure predicate, including
the prime two. This states the unconditional criterion directly for a least witness. -/
theorem exists_least_prime_primePow_chebyshevBudget {n p a : ℕ} (hn : 1 < n) (ho : Odd n)
    (hp : p.Prime) (hp2 : p ≠ 2) (ha : 0 < a) (hdiv : p ^ a ∣ n) (B M k : ℕ) (hB : 1 < B)
    (hprimecount :
      (M : ℝ) * Real.log B ≤ (B : ℝ) * Real.log 2 - Real.log (B + 1) - 2 * Real.sqrt B * Real.log B)
    (hsize : B ^ k < p ^ a) (hbudget : (p - 1) * k ^ k < (M + 1 - k) ^ k) :
    ∃ r : ℕ,
      r.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) ∧
        r ≤ B ∧ ∀ s : ℕ, s.Prime → ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) → r ≤ s := by
  classical
  obtain ⟨r, hr, hb, hf⟩ :=
    exists_prime_primePow_chebyshevBudget hn ho hp hp2 ha hdiv B M k hB hprimecount hsize hbudget
  have hex : ∃ s : ℕ, s.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) := ⟨r, hr, hf⟩
  exact
    ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2,
      (Nat.find_min' hex ⟨hr, hf⟩).trans hb, fun s hs hfail ↦ Nat.find_min' hex ⟨hs, hfail⟩⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
