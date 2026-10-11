/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Jacobi.Computation
public import PseudoPrime.PrimeTest.Precheck
public import PseudoPrime.PrimeTest.StrongLucas.NoGcd

/-! # Compatibility names for the lower-level batched Jacobi computation

The implementation and its proofs live in NumberTheory, independent of PrimeTest.
These aliases preserve existing qualified source references and theorem contracts.
-/

@[expose] public section

namespace PseudoPrime.PrimeTest.ReferenceArithmetic

export PseudoPrime.NumberTheory.Jacobi
  (jacobiSign2 oddPart_pos oddPart_le oddPart_odd jacobiRoundSign jacobiRoundSign_mul
    jacobiNat jacobiNat_eq jacobiSigned jacobiSign4 jacobiSigned_eq)

end PseudoPrime.PrimeTest.ReferenceArithmetic
