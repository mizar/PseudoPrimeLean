/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.MillerRabin.Defs

/-!
# Strong Miller–Rabin executable specification
-/

@[expose] public section

namespace PseudoPrime.PrimeTest

/--
For any natural input `n` and base `a`, executable acceptance is exactly the finite
Strong Miller–Rabin proposition `IsStrongMillerRabinProbablePrime n a`.
The proof unfolds both interfaces, replaces executable modular powers by mathematical powers,
and rewrites the Boolean decision. This bridge supplies the specification for prime-pass proofs;
it does not require or establish primality or coprimality by itself.
-/
theorem strongMillerRabinWithBase_eq_true_iff {n a : ℕ} :
    strongMillerRabinWithBase n a = true ↔ IsStrongMillerRabinProbablePrime n a := by
  simp only [strongMillerRabinWithBase, IsStrongMillerRabinProbablePrime, zmodPow_eq_pow,
    zmodPowProof_eq_pow, decide_eq_true_eq]

/--
The base-two executable accepts `n` exactly when the finite Strong condition holds at base `2`.
No primality or parity hypothesis is needed for this totalized equivalence. The proof is the
general-base specification specialized to `a = 2`. Prechecked wrappers use this bridge to
connect their arithmetic branch with the mathematical Strong Miller–Rabin condition.
-/
theorem strongMillerRabinBase2_eq_true_iff {n : ℕ} :
    strongMillerRabinBase2 n = true ↔ IsStrongMillerRabinProbablePrime n 2 := by
  exact strongMillerRabinWithBase_eq_true_iff

end PseudoPrime.PrimeTest
