/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.Lucas.FiniteField
public import PseudoPrime.PrimeTest.LucasV.Spec

/-!
# Prime completeness for the Lucas-V test

This file connects the Jacobi `-1` branch to the finite-field Lucas-V bridge.
-/

@[expose] public section

namespace PseudoPrime.PrimeTest

/--
A prime input passes the Lucas-V comparison under the discriminant and Jacobi hypotheses.
Assume `n.Prime`, `D = P * P - 4 * Q`, and `jacobiSym D n = -1`.
The Jacobi hypothesis makes the discriminant a nonsquare in the prime field; the finite-field
Lucas identity gives `V_(n+1) = 2Q`. The executable specification then yields `true`.
Strengthened BPSW and the guarded Lucas-V decision adapter use this prime-pass implication.
-/
theorem lucasVWithParams_of_prime {n : ℕ} (hn : n.Prime) (D P Q : ℤ) (hdisc : D = P * P - 4 * Q)
    (hjacobi : jacobiSym D n = -1) : lucasVWithParams n D P Q = true := by
  let _ : Fact n.Prime := ⟨hn⟩
  have hdiscZ : ¬IsSquare ((P : ZMod n) * (P : ZMod n) - 4 * (Q : ZMod n)) := by
    simpa only [hdisc, Int.cast_sub, Int.cast_mul, Int.cast_ofNat] using
      (lucasDiscriminant_not_isSquare_of_jacobi_neg_one hjacobi)
  rw [lucasVWithParams_eq_true_iff n D P Q hdisc]
  refine ⟨hjacobi, ?_⟩
  exact lucasVZMod_prime_eq_two_mul n P Q hdiscZ

end PseudoPrime.PrimeTest
