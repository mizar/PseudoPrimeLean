/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.MillerRabin.Decomposition

/-! # Least rejecting prime extraction -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A bounded rejecting prime yields a least rejecting prime with the same
bound. This bridge lets the endpoint witness theorems expose minimum-witness
results without repeating the `Nat.find` argument. -/
theorem exists_least_prime_reject_of_exists_prime_reject {N : ℕ} [NeZero N] {B : ℝ}
    (h : ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ B ∧ ¬PrimeTest.StrongMillerRabinPass N (p : ZMod N)) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ B ∧
        ¬PrimeTest.StrongMillerRabinPass N (p : ZMod N) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass N (q : ZMod N) → p ≤ q := by
  classical
  let hex : ∃ q : ℕ, q.Prime ∧ ¬PrimeTest.StrongMillerRabinPass N (q : ZMod N) := by
    exact ⟨h.choose, h.choose_spec.1, h.choose_spec.2.2⟩
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, ?_, (Nat.find_spec hex).2, ?_⟩
  · exact
      (Nat.cast_le.mpr (Nat.find_min' hex ⟨h.choose_spec.1, h.choose_spec.2.2⟩)).trans
        h.choose_spec.2.1
  · intro q hq hf
    exact Nat.find_min' hex ⟨hq, hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
