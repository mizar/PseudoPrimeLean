/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.EulerJacobi.Defs

/-!
# Euler–Jacobi executable specification
-/

@[expose] public section

namespace PseudoPrime.PrimeTest

/--
Propositional raw Euler–Jacobi condition for natural `n` and natural base `a`.
It is the equality `a^(n / 2) = jacobiSym a n` after casting both sides to `ZMod n`.
No primality, parity, or coprimality hypotheses are built into the definition.
The executable specification identifies this proposition with the Boolean comparison's acceptance.
-/
def IsEulerJacobiProbablePrime (n a : ℕ) : Prop :=
  (a : ZMod n) ^ (n / 2) = (jacobiSym (a : ℤ) n : ZMod n)

/--
Raw natural-base executable acceptance is equivalent to `IsEulerJacobiProbablePrime n a`.
There are no extra premises. Unfolding the Boolean decision and the proposition proves the
result by `decide_eq_true_eq`. Prime completeness uses this bridge to prove acceptance
from the prime-field Legendre-symbol power formula.
-/
theorem eulerJacobiWithBase_eq_true_iff {n a : ℕ} :
    eulerJacobiWithBase n a = true ↔ IsEulerJacobiProbablePrime n a := by
  simp only [eulerJacobiWithBase, IsEulerJacobiProbablePrime, decide_eq_true_eq]

/-! The signed interface has the same specification with an integer base. -/

/--
Signed-base propositional Euler–Jacobi condition in `ZMod n`.
For natural `n` and integer `a`, require `a^(n / 2)` to equal the cast of `jacobiSym a n`.
The cast gives the intended modular meaning for negative bases without an explicit normalization
step. This proposition is the mathematical interface of `eulerJacobiWithIntBase`.
-/
def IsEulerJacobiProbablePrimeInt (n : ℕ) (a : ℤ) : Prop :=
  (a : ZMod n) ^ (n / 2) = (jacobiSym a n : ZMod n)

/--
Signed executable acceptance is exactly `IsEulerJacobiProbablePrimeInt n a`.
This all-input equivalence requires no normalization, parity, or coprimality premise.
The proof unfolds the identical equality and rewrites the Boolean decision.
Signed prime-pass results use it to connect residue-ring identities to executable acceptance.
-/
theorem eulerJacobiWithIntBase_eq_true_iff {n : ℕ} {a : ℤ} :
    eulerJacobiWithIntBase n a = true ↔ IsEulerJacobiProbablePrimeInt n a := by
  simp only [eulerJacobiWithIntBase, IsEulerJacobiProbablePrimeInt, decide_eq_true_eq]

end PseudoPrime.PrimeTest
