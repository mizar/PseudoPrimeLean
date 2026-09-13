/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.PrimeTest.MillerRabin.Defs

/-!
# Strong Miller–Rabin executable specification
-/

namespace PseudoPrime.PrimeTest

/-- The executable test is equivalent to the finite Strong condition. -/
theorem strongMillerRabinWithBase_eq_true_iff {n a : ℕ} :
    strongMillerRabinWithBase n a = true ↔ IsStrongMillerRabinProbablePrime n a := by
  simp only [strongMillerRabinWithBase, IsStrongMillerRabinProbablePrime, zmodPow_eq_pow,
    zmodPowProof_eq_pow, decide_eq_true_eq]

/-- The base-2 wrapper has the same Strong Miller–Rabin specification. -/
theorem strongMillerRabinBase2_eq_true_iff {n : ℕ} :
    strongMillerRabinBase2 n = true ↔ IsStrongMillerRabinProbablePrime n 2 := by
  exact strongMillerRabinWithBase_eq_true_iff

end PseudoPrime.PrimeTest
