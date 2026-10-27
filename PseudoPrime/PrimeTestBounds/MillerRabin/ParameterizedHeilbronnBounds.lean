/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.ParameterizedHeilbronnFermatBound
public import PseudoPrime.PrimeTestBounds.MillerRabin.FermatQuotientAsymptoticTransfer

/-! # Arbitrary MR log exponents above 28/15 on odd nonsquarefree inputs -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For any fixed A>28/15, every sufficiently large odd nonsquarefree n has a prime
MR witness at most log(n)^A. Apply the parameterized proved Fermat bound. -/
theorem eventually_exists_prime_witness_le_exponent_of_not_squarefree {A : ℝ}
    (hA : (28 / 15 : ℝ) < A) :
    Filter.Eventually
      (fun n : ℕ ↦
        1 < n →
          Odd n →
          ¬Squarefree n →
          ∃ q : ℕ,
            q.Prime ∧ (q : ℝ) ≤ (Real.log n) ^ A ∧ ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n))
      Filter.atTop := by
  have hAp : 0 < A := lt_trans (by norm_num only : (0 : ℝ) < 28 / 15) hA
  apply eventually_exists_prime_witness_le_log_power_of_fermat_quotient_bound hAp
  apply
    (NumberTheory.Heilbronn.eventually_exists_prime_nontrivial_power_le_log_power_of_exponent
        hA).mono
  intro p h hp hp2
  obtain ⟨q, hq, hb, hpow⟩ := h hp hp2
  exact ⟨q, hq.pos, hb, hpow⟩

/-- For any fixed A>28/15 the same eventual bound holds for the least prime witness.
Minimize the rejecting-prime predicate after applying the constructed bound. -/
theorem eventually_exists_least_prime_witness_le_exponent_of_not_squarefree {A : ℝ}
    (hA : (28 / 15 : ℝ) < A) :
    Filter.Eventually
      (fun n : ℕ ↦
        1 < n →
          Odd n →
          ¬Squarefree n →
          ∃ q : ℕ,
            q.Prime ∧
              ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) ∧
              (q : ℝ) ≤ (Real.log n) ^ A ∧
              ∀ s : ℕ, s.Prime → ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) → q ≤ s)
      Filter.atTop := by
  classical
  apply (eventually_exists_prime_witness_le_exponent_of_not_squarefree hA).mono
  intro n h hn ho hns
  obtain ⟨q, hq, hb, hf⟩ := h hn ho hns
  have hex : ∃ s : ℕ, s.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) := ⟨q, hq, hf⟩
  exact
    ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2,
      (Nat.cast_le.mpr (Nat.find_min' hex ⟨hq, hf⟩)).trans hb, fun s hs hfail ↦
      Nat.find_min' hex ⟨hs, hfail⟩⟩

/-- For each fixed 0<epsilon<2/15, the least prime MR witness is eventually at most
log(n)^(2-epsilon) on all odd nonsquarefree inputs. The threshold can depend on epsilon;
no endpoint epsilon=2/15 and no squarefree input are asserted. -/
theorem eventually_exists_least_prime_witness_le_two_sub_epsilon_of_not_squarefree {epsilon : ℝ}
    (_he0 : 0 < epsilon) (he1 : epsilon < 2 / 15) :
    Filter.Eventually
      (fun n : ℕ ↦
        1 < n →
          Odd n →
          ¬Squarefree n →
          ∃ q : ℕ,
            q.Prime ∧
              ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) ∧
              (q : ℝ) ≤ (Real.log n) ^ (2 - epsilon) ∧
              ∀ s : ℕ, s.Prime → ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) → q ≤ s)
      Filter.atTop := by
  have hA : (28 / 15 : ℝ) < 2 - epsilon := by linarith only [he1]
  exact eventually_exists_least_prime_witness_le_exponent_of_not_squarefree hA

end PseudoPrime.PrimeTestBounds.MillerRabin
