/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.StrongLucas.FromLucas
public import PseudoPrime.PrimeTest.StrongLucas.Spec

/-!
# Prime completeness for the Strong Lucas test

This file connects the Jacobi `-1` branch to the finite-field Lucas bridge.
-/

@[expose] public section

namespace PseudoPrime.PrimeTest

/--
A prime modulus passes Strong Lucas in the Jacobi-minus-one branch.
Assume `n.Prime`, the discriminant equation `D = P * P - 4 * Q`, and `jacobiSym D n = -1`.
The finite-field bridge gives `U_(n+1) = 0`; the selected-index theorem identifies this with
the Lucas index, and the Lucas-to-Strong bridge finds a successful finite branch.
The executable specification converts that branch to `true` for BPSW prime completeness.
-/
theorem strongLucasWithParams_of_prime {n : ℕ} (hn : n.Prime) (D P Q : ℤ)
    (hdisc : D = P * P - 4 * Q) (hjacobi : jacobiSym D n = -1) :
    strongLucasWithParams n D P Q = true := by
  let _ : Fact n.Prime := ⟨hn⟩
  have hdiscZ : ¬IsSquare ((P : ZMod n) * (P : ZMod n) - 4 * (Q : ZMod n)) := by
    simpa only [hdisc, Int.cast_sub, Int.cast_mul, Int.cast_ofNat] using
      (lucasDiscriminant_not_isSquare_of_jacobi_neg_one hjacobi)
  have hzero : lucasUZMod n P Q (lucasProbablePrimeIndex n D) = 0 := by
    rw [lucasProbablePrimeIndex_of_jacobi_eq_neg_one hjacobi]
    exact lucasUZMod_prime_eq_zero n P Q hdiscZ
  rw [strongLucasWithParams_eq_true_iff n D P Q hdisc]
  exact
    isStrongLucasProbablePrime_of_lucasUZMod_index_zero (LucasParams.ofDiscriminant D P Q hdisc)
      hzero

end PseudoPrime.PrimeTest
