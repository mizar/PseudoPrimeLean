/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.PrimeTest.EulerJacobi.Spec

/-!
# Prime inputs for the Euler–Jacobi test

The prime case is proved directly in `ZMod` from the Legendre-symbol power
formula, avoiding any conversion of the Jacobi value to a natural residue.
-/

namespace PseudoPrime.PrimeTest

private theorem eulerJacobi_condition_of_prime {p a : ℕ} (hp : p.Prime) :
    IsEulerJacobiProbablePrime p a := by
  change (a : ZMod p) ^ (p / 2) = (jacobiSym (a : ℤ) p : ZMod p)
  rw [← @jacobiSym.legendreSym.to_jacobiSym p ⟨hp⟩ (a : ℤ)]
  simpa only [Int.cast_natCast] using (@legendreSym.eq_pow p ⟨hp⟩ (a : ℤ)).symm

/-- A prime modulus passes the Euler–Jacobi test in the `n / 2` formulation. -/
theorem eulerJacobiWithBase_of_prime_of_ne_two {p a : ℕ} (hp : p.Prime) :
    eulerJacobiWithBase p a = true := by
  apply (eulerJacobiWithBase_eq_true_iff).2
  exact eulerJacobi_condition_of_prime hp

private theorem eulerJacobi_condition_of_two {a : ℕ} : IsEulerJacobiProbablePrime 2 a := by
  exact eulerJacobi_condition_of_prime Nat.prime_two

/-- A natural-number base coprime to a prime modulus passes the test. -/
theorem eulerJacobiWithBase_of_prime {p a : ℕ} (hp : p.Prime) (ha : Nat.Coprime a p) :
    eulerJacobiWithBase p a = true := by
  rcases eq_or_ne p 2 with rfl | _hp2
  · apply (eulerJacobiWithBase_eq_true_iff).2
    exact eulerJacobi_condition_of_two
  · exact eulerJacobiWithBase_of_prime_of_ne_two hp

/-- Every signed base passes for a prime modulus in the `n / 2` formulation. -/
theorem eulerJacobiWithIntBase_of_prime {p : ℕ} (hp : p.Prime) (a : ℤ) :
    eulerJacobiWithIntBase p a = true := by
  apply (eulerJacobiWithIntBase_eq_true_iff).2
  change (a : ZMod p) ^ (p / 2) = (jacobiSym a p : ZMod p)
  rw [← @jacobiSym.legendreSym.to_jacobiSym p ⟨hp⟩ a]
  exact (@legendreSym.eq_pow p ⟨hp⟩ a).symm

end PseudoPrime.PrimeTest
