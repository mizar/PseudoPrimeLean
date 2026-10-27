/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.ParameterizedHeilbronnBounds

/-! # Reduction of the remaining MR exponent problem to squarefree composites -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For A>28/15, an eventual prime-witness bound on all odd composites is equivalent
to the same bound on squarefree odd composites. The nonsquarefree complement is already proved. -/
theorem eventually_prime_witness_bound_iff_squarefree {A : ℝ} (hA : (28 / 15 : ℝ) < A) :
    (Filter.Eventually
        (fun n : ℕ ↦
          1 < n →
            Odd n →
            ¬n.Prime →
            ∃ q : ℕ,
              q.Prime ∧
                (q : ℝ) ≤ (Real.log n) ^ A ∧ ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n))
        Filter.atTop) ↔
      (Filter.Eventually
        (fun n : ℕ ↦
          1 < n →
            Odd n →
            ¬n.Prime →
            Squarefree n →
            ∃ q : ℕ,
              q.Prime ∧
                (q : ℝ) ≤ (Real.log n) ^ A ∧ ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n))
        Filter.atTop) := by
  constructor
  · intro h
    exact h.mono (fun n hn hng ho hcomp _ ↦ hn hng ho hcomp)
  · intro hs
    filter_upwards [hs, eventually_exists_prime_witness_le_exponent_of_not_squarefree hA] with n hsq
      hns hn ho hcomp
    by_cases hsf : Squarefree n
    · exact hsq hn ho hcomp hsf
    · exact hns hn ho hsf

/-- For A>28/15, the same equivalence holds for the least prime MR witness.
Combine the squarefree premise with the proved nonsquarefree result, using the larger threshold. -/
theorem eventually_least_prime_witness_bound_iff_squarefree {A : ℝ} (hA : (28 / 15 : ℝ) < A) :
    (Filter.Eventually
        (fun n : ℕ ↦
          1 < n →
            Odd n →
            ¬n.Prime →
            ∃ q : ℕ,
              q.Prime ∧
                ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) ∧
                (q : ℝ) ≤ (Real.log n) ^ A ∧
                ∀ s : ℕ, s.Prime → ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) → q ≤ s)
        Filter.atTop) ↔
      (Filter.Eventually
        (fun n : ℕ ↦
          1 < n →
            Odd n →
            ¬n.Prime →
            Squarefree n →
            ∃ q : ℕ,
              q.Prime ∧
                ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) ∧
                (q : ℝ) ≤ (Real.log n) ^ A ∧
                ∀ s : ℕ, s.Prime → ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) → q ≤ s)
        Filter.atTop) := by
  constructor
  · intro h
    exact h.mono (fun n hn hng ho hcomp _ ↦ hn hng ho hcomp)
  · intro hs
    filter_upwards [hs, eventually_exists_least_prime_witness_le_exponent_of_not_squarefree hA] with
      n hsq hns hn ho hcomp
    by_cases hsf : Squarefree n
    · exact hsq hn ho hcomp hsf
    · exact hns hn ho hsf

end PseudoPrime.PrimeTestBounds.MillerRabin
