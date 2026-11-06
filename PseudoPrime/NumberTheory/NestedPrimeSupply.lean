/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Combinatorics.NestedFiniteSupply
public import Mathlib.NumberTheory.PrimeCounting

/-! # Nested finite prime supplies -/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- Monotone prime cutoffs and certified monotone lower bounds for their prime
counts admit nested prime sets of exactly the requested cardinalities. Each
selected prime is bounded by its own cutoff, so successive set differences
form disjoint supplies without requiring prime counts in short intervals. -/
theorem exists_nested_prime_supply (b m : ℕ → ℕ) (hb : Monotone b) (hm : Monotone m)
    (hs : ∀ i, m i ≤ (b i).primeCounting) :
    ∃ S : ℕ → Finset ℕ, Monotone S ∧ ∀ i, (S i).card = m i ∧ ∀ p ∈ S i, p.Prime ∧ p ≤ b i := by
  have hs' : ∀ i, m i ≤ ((b i).primesLE).card := by
    intro i
    rw [Nat.primesLE_card_eq_primeCounting]
    exact hs i
  obtain ⟨S, hS, hdata⟩ :=
    Combinatorics.exists_nested_supply (fun i ↦ (b i).primesLE) m (Nat.primesLE_mono.comp hb) hm hs'
  refine ⟨S, hS, ?_⟩
  intro i
  refine ⟨(hdata i).2, ?_⟩
  intro p hp
  have h := Nat.mem_primesLE.mp ((hdata i).1 hp)
  exact ⟨h.2, h.1⟩

end PseudoPrime.NumberTheory
