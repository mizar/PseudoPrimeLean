/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.ReferenceArithmetic
public import PseudoPrime.NumberTheory.Jacobi.Fuel
public import PseudoPrime.NumberTheory.Jacobi.Fast

/-! # Prime-test compatibility and executable Jacobi decisions

The fuel-bounded implementation is shared with the NumberTheory layer.
This module preserves the old names and supplies the prime-test decision interface.
-/

@[expose] public section

namespace PseudoPrime.PrimeTest.ReferenceArithmetic

export PseudoPrime.NumberTheory.Jacobi (jacobiNat_round jacobiNatBatchedFuel
  jacobiNatBatchedFuel_none_nonstop jacobiNatBatchedFuel_result jacobiNatBatchedFuel_complete
  jacobiNatBatchedFuel_eq jacobiNatBatched jacobiNatBatched_eq jacobiSignedBatched
  jacobiSignedBatched_eq jacobiNormalizedBatched jacobiNormalizedBatched_eq
  jacobiNatBatchedFuel_log2 jacobiNatBatchedFuel_ne_none jacobiStepBound_mono jacobiNormalized_lt
  jacobiNormalizedBatchedFuel_eq jacobiNormalizedBatchedFuel_log2 jacobiNatBatchedFuel_sound)

/-- Executable Jacobi entry on every integer numerator and natural modulus.
Nonzero denominators use the symbol-only recursion without gcd computation or fuel selection.
The factor-at-two correction and zero-input branches preserve mathlib conventions.
This entry supplies executable guards while their proofs continue to use jacobiSym. -/
def jacobiExecutable (a : ℤ) (n : ℕ) : ℤ :=
  NumberTheory.jacobiSymFast a n

/-- The executable entry agrees with jacobiSym on all inputs.
The all-input compatibility theorem covers odd, even and zero denominators.
This equality transfers existing stopping predicates and proof-carrying classifications. -/
theorem jacobiExecutable_eq (a : ℤ) (n : ℕ) : jacobiExecutable a n = jacobiSym a n := by
  exact NumberTheory.jacobiSymFast_eq a n

/-- Decide a mathematical Jacobi equality using the certified executable entry.
The returned true or false evidence is transported through jacobiExecutable_eq.
This lets dependent consumers retain their existing jacobiSym hypotheses. -/
def jacobiEqDecidable (a : ℤ) (n : ℕ) (z : ℤ) : Decidable (jacobiSym a n = z) :=
  if hj : jacobiExecutable a n = z then isTrue ((jacobiExecutable_eq a n).symm.trans hj)
  else isFalse (fun h ↦ hj ((jacobiExecutable_eq a n).trans h))

/-- The executable equality decision agrees with the existing decision on all inputs.
Subsingleton uniqueness identifies both decisions and their proof evidence.
This equality preserves dependent classifications while changing their computation. -/
theorem jacobiEqDecidable_eq (a : ℤ) (n : ℕ) (z : ℤ) :
    jacobiEqDecidable a n z = (inferInstance : Decidable (jacobiSym a n = z)) := by
  exact Subsingleton.elim _ _

end PseudoPrime.PrimeTest.ReferenceArithmetic
