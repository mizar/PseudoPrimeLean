/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Basic.Real.Basic
public import PseudoPrime.PrimeTest.MillerRabin.Decomposition

/-! # Combining bounds for the least prime strong-MR witness -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Combine two least-prime witness bounds by choosing the smaller numerical
cutoff. The selected witness remains least among all rejecting primes. -/
theorem least_prime_witness_bound_min {n : ℕ} {A B : ℝ}
    (hA :
      ∃ p : ℕ,
        p.Prime ∧
          ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
          (p : ℝ) ≤ A ∧ ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q)
    (hB :
      ∃ p : ℕ,
        p.Prime ∧
          ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
          (p : ℝ) ≤ B ∧
          ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ min A B ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  rcases hA with ⟨pA, hpA, hfailA, hboundA, hminA⟩
  rcases hB with ⟨pB, hpB, hfailB, hboundB, hminB⟩
  by_cases hAB : A ≤ B
  · refine ⟨pA, hpA, hfailA, ?_, hminA⟩
    rw [min_eq_left hAB]
    exact hboundA
  · have hBA : B ≤ A := le_of_not_ge hAB
    refine ⟨pB, hpB, hfailB, ?_, hminB⟩
    rw [min_eq_right hBA]
    exact hboundB

end PseudoPrime.PrimeTestBounds.MillerRabin
