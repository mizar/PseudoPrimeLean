/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.PrimeTest.EulerJacobi.Defs

/-!
# Euler–Jacobi executable specification
-/

namespace PseudoPrime.PrimeTest

/-- The mathematical Euler–Jacobi condition for a natural-number base. -/
def IsEulerJacobiProbablePrime (n a : ℕ) : Prop :=
  (a : ZMod n) ^ (n / 2) = (jacobiSym (a : ℤ) n : ZMod n)

/-- The executable Euler–Jacobi test is equivalent to its Boolean specification. -/
theorem eulerJacobiWithBase_eq_true_iff {n a : ℕ} :
    eulerJacobiWithBase n a = true ↔ IsEulerJacobiProbablePrime n a := by
  simp only [eulerJacobiWithBase, IsEulerJacobiProbablePrime, decide_eq_true_eq]

/-! The signed interface has the same specification with an integer base. -/

/-- The mathematical Euler–Jacobi condition for an integer base. -/
def IsEulerJacobiProbablePrimeInt (n : ℕ) (a : ℤ) : Prop :=
  (a : ZMod n) ^ (n / 2) = (jacobiSym a n : ZMod n)

/-- The signed executable test is equivalent to its normalized specification. -/
theorem eulerJacobiWithIntBase_eq_true_iff {n : ℕ} {a : ℤ} :
    eulerJacobiWithIntBase n a = true ↔ IsEulerJacobiProbablePrimeInt n a := by
  simp only [eulerJacobiWithIntBase, IsEulerJacobiProbablePrimeInt, decide_eq_true_eq]

end PseudoPrime.PrimeTest
