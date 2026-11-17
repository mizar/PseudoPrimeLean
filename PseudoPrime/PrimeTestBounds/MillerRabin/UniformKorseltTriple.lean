/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.Data.Nat.PadicValNat
public import Mathlib.Data.Nat.PrimeFin

/-! # Uniform Korselt triples and the finite-index threshold -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The exceptional squarefree Korselt triple with uniform predecessor valuations.
This predicate packages the arithmetic alternative in the finite-index classification
for use in the nonexceptional witness branch. -/
def UniformKorseltTriple (n : ℕ) : Prop :=
  Squarefree n ∧
    n.primeFactors.card = 3 ∧
    (∀ p : ℕ, p.Prime → p ∣ n → p - 1 ∣ n - 1) ∧
    (∀ p q : ℕ, p.Prime → q.Prime → p ∣ n → q ∣ n → padicValNat 2 (p - 1) = padicValNat 2 (q - 1))

end PseudoPrime.PrimeTestBounds.MillerRabin
