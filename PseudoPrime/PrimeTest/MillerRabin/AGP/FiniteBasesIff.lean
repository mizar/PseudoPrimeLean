/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.MillerRabin.AGP.FiniteBases
public import PseudoPrime.PrimeTest.MillerRabin.Decomposition

/-! # Decomposition equivalences for the AGP finite-base propositions -/

@[expose] public section

namespace PseudoPrime.PrimeTest.MillerRabin.AGP

/--
The AGP finite-prime-base proposition stated using the canonical strong
Miller–Rabin pass predicate from `Decomposition`.
-/
def AGPFinitePrimeBasesWithDecomposition : Prop :=
  ∀ S : Finset ℕ,
    (∀ p ∈ S, Nat.Prime p) →
      ∃ a : ℕ,
        Nat.IsCarmichael a ∧ ∀ p ∈ S, PseudoPrime.PrimeTest.StrongMillerRabinPass a (p : ZMod a)

/--
The unbounded-initial-base proposition stated using the canonical strong
Miller–Rabin pass predicate from `Decomposition`.
-/
def AGPInitialBasesUnboundedWithDecomposition : Prop :=
  ∀ B C : ℕ,
    ∃ a : ℕ,
      C < a ∧
        Nat.IsCarmichael a ∧
        ∀ b : ℕ, 0 < b → b ≤ B → PseudoPrime.PrimeTest.StrongMillerRabinPass a (b : ZMod a)

/--
The decomposition-free and decomposition-based formulations of the AGP finite
prime-base proposition are equivalent.
-/
theorem agpFinitePrimeBases_iff : AGPFinitePrimeBases ↔ AGPFinitePrimeBasesWithDecomposition := by
  rfl

/--
The decomposition-free and decomposition-based formulations of the AGP
unbounded-initial-base proposition are equivalent.
-/
theorem agpInitialBasesUnbounded_iff :
    AGPInitialBasesUnbounded ↔ AGPInitialBasesUnboundedWithDecomposition := by rfl

end PseudoPrime.PrimeTest.MillerRabin.AGP
