/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.PrimeCharacterWitnessExtraction
public import PseudoPrime.PrimeTest.MillerRabin.Decomposition

/-! # Passing from integer character witnesses to prime MR witnesses -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Suppose every MR passing integer has character value one. A positive
integer with character value neither zero nor one gives a prime MR witness
at most that integer, coprime to the character modulus. Extract a prime divisor
and use the pass-containment hypothesis. No analytic estimate is supplied here. -/
theorem exists_prime_witness_of_integer_character_witness {R : Type*} [CommMonoidWithZero R]
    [Nontrivial R] {n q a : ℕ} (χ : DirichletCharacter R q)
    (hpass : ∀ b : ℕ, PrimeTest.StrongMillerRabinPass n (b : ZMod n) → χ (b : ZMod q) = 1)
    (ha : 0 < a) (hz : χ (a : ZMod q) ≠ 0) (hne : χ (a : ZMod q) ≠ 1) :
    ∃ p : ℕ,
      p.Prime ∧
        p ≤ a ∧
        p.Coprime q ∧
        χ (p : ZMod q) ≠ 0 ∧
        χ (p : ZMod q) ≠ 1 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  obtain ⟨p, hp, _, hpa, hcop, hp0, hp1⟩ :=
    NumberTheory.exists_prime_divisor_character_nonzero_ne_one χ ha hz hne
  exact ⟨p, hp, hpa, hcop, hp0, hp1, fun h ↦ hp1 (hpass p h)⟩

/-- Under the same character hypotheses, the least prime MR witness is at
most the integer witness. Minimize over all MR rejecting prime bases.
The minimum need not be coprime to the character modulus, so no such claim
is included for the least witness. The larger extracted witness is coprime. -/
theorem exists_least_prime_witness_of_integer_character_witness {R : Type*} [CommMonoidWithZero R]
    [Nontrivial R] {n q a : ℕ} (χ : DirichletCharacter R q)
    (hpass : ∀ b : ℕ, PrimeTest.StrongMillerRabinPass n (b : ZMod n) → χ (b : ZMod q) = 1)
    (ha : 0 < a) (hz : χ (a : ZMod q) ≠ 0) (hne : χ (a : ZMod q) ≠ 1) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        p ≤ a ∧ ∀ r : ℕ, r.Prime → ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) → p ≤ r := by
  classical
  obtain ⟨p, hp, hpa, _, _, _, hf⟩ :=
    exists_prime_witness_of_integer_character_witness χ hpass ha hz hne
  have hex : ∃ r : ℕ, r.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := ⟨p, hp, hf⟩
  exact
    ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2,
      (Nat.find_min' hex ⟨hp, hf⟩).trans hpa, fun r hr hfail ↦ Nat.find_min' hex ⟨hr, hfail⟩⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
