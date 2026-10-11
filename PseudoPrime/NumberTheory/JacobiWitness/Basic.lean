/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Data.Nat.Find
public import PseudoPrime.NumberTheory.Jacobi.Basic

/-!
# Least odd-prime Jacobi witnesses

This file defines the mathematical witness sets underlying `p_ne1(n)` and `p_negOne(n)` and
their least elements.  Existence is explicit so that the unconditional order theory remains
independent of the arithmetic construction establishing that nonsquares have witnesses.
-/

@[expose] public section

namespace PseudoPrime.NumberTheory

/--
`primeNeOneWitnessSet n` is the set of odd primes `p` for which `J(n | p) ≠ 1`.  It represents
the admissible witnesses in the definition of `p_ne1(n)`.
-/
def primeNeOneWitnessSet (n : ℕ) : Set ℕ :=
  {p | p.Prime ∧ Odd p ∧ jacobiSym n p ≠ 1}

/--
`primeNegOneWitnessSet n` is the set of odd primes `p` for which `J(n | p) = -1`.  It represents
the admissible witnesses in the definition of `p_negOne(n)`.
-/
def primeNegOneWitnessSet (n : ℕ) : Set ℕ :=
  {p | p.Prime ∧ Odd p ∧ jacobiSym n p = -1}

/-- Every `-1` odd-prime witness is also a `≠ 1` odd-prime witness. -/
theorem primeNegOneWitnessSet.subset_primeNeOneWitnessSet (n : ℕ) :
    primeNegOneWitnessSet n ⊆ primeNeOneWitnessSet n := by
  intro p hp
  exact
    ⟨hp.1, hp.2.1, by
      rw [hp.2.2]
      norm_num only⟩

/-- Nonemptiness of the `-1` witness set implies nonemptiness of the `≠ 1` witness set. -/
theorem primeNeOneWitnessSet_nonempty_of_negOne {n : ℕ} (h : (primeNegOneWitnessSet n).Nonempty) :
    (primeNeOneWitnessSet n).Nonempty :=
  h.mono (primeNegOneWitnessSet.subset_primeNeOneWitnessSet n)

/--
`primeNeOneWitness n h` is the least odd prime whose Jacobi value for `n` is not `1`.  The proof
`h` records the well-definedness obligation separately from minimization.
-/
noncomputable def primeNeOneWitness (n : ℕ) (h : (primeNeOneWitnessSet n).Nonempty) : ℕ := by
  classical exact Nat.find h

/--
`primeNegOneWitness n h` is the least odd prime whose Jacobi value for `n` is `-1`.  Its
existence argument is supplied separately, so the definition requires no analytic assumptions.
-/
noncomputable def primeNegOneWitness (n : ℕ) (h : (primeNegOneWitnessSet n).Nonempty) : ℕ := by
  classical exact Nat.find h

/-- The least `≠ 1` odd-prime witness belongs to its witness set. -/
theorem primeNeOneWitness_mem (n : ℕ) (h : (primeNeOneWitnessSet n).Nonempty) :
    primeNeOneWitness n h ∈ primeNeOneWitnessSet n := by classical exact Nat.find_spec h

/-- The least `-1` odd-prime witness belongs to its witness set. -/
theorem primeNegOneWitness_mem (n : ℕ) (h : (primeNegOneWitnessSet n).Nonempty) :
    primeNegOneWitness n h ∈ primeNegOneWitnessSet n := by classical exact Nat.find_spec h

/-- Every `≠ 1` odd-prime witness is at least the least such witness. -/
theorem primeNeOneWitness_le (n : ℕ) (h : (primeNeOneWitnessSet n).Nonempty) {p : ℕ}
    (hp : p ∈ primeNeOneWitnessSet n) : primeNeOneWitness n h ≤ p := by
  classical exact Nat.find_min' h hp

/-- Every `-1` odd-prime witness is at least the least such witness. -/
theorem primeNegOneWitness_le (n : ℕ) (h : (primeNegOneWitnessSet n).Nonempty) {p : ℕ}
    (hp : p ∈ primeNegOneWitnessSet n) : primeNegOneWitness n h ≤ p := by
  classical exact Nat.find_min' h hp

/--
The least `≠ 1` witness is no larger than the least `-1` witness.  Both occurrences use the
same input `n`; nonemptiness of the first set is derived from that of the second.
-/
theorem primeNeOneWitness_le_primeNegOneWitness (n : ℕ) (h : (primeNegOneWitnessSet n).Nonempty) :
    primeNeOneWitness n (primeNeOneWitnessSet_nonempty_of_negOne h) ≤ primeNegOneWitness n h := by
  apply primeNeOneWitness_le
  exact primeNegOneWitnessSet.subset_primeNeOneWitnessSet n (primeNegOneWitness_mem n h)

end PseudoPrime.NumberTheory
