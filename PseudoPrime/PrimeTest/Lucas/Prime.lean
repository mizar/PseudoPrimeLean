/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.Lucas.FiniteField

/-! # Prime completeness of the Lucas U test in the Jacobi minus-one branch -/

@[expose] public section

namespace PseudoPrime.PrimeTest

/--
Every prime modulus passes the Lucas `U` comparison in the Jacobi-minus-one branch.
Assume `n.Prime`, `D = P * P - 4 * Q`, and `jacobiSym D n = -1`.
The Jacobi value gives a nonsquare discriminant in the prime field, whose Lucas bridge
proves `U_(n+1) = 0`. The selected-index identity and executable specification yield `true`.
The guarded Lucas adapter uses this implication; other Jacobi branches are not covered.
-/
theorem lucasWithParams_of_prime {n : ℕ} (hn : n.Prime) (D P Q : ℤ) (hdisc : D = P * P - 4 * Q)
    (hjacobi : jacobiSym D n = -1) : lucasWithParams n D P Q = true := by
  let _ : Fact n.Prime := ⟨hn⟩
  have hns := lucasDiscriminant_not_isSquare_of_jacobi_neg_one hjacobi
  have hd : ¬IsSquare ((P : ZMod n) * (P : ZMod n) - 4 * (Q : ZMod n)) := by
    simpa only [hdisc, Int.cast_sub, Int.cast_mul, Int.cast_ofNat] using hns
  exact
    (lucasWithParams_eq_true_iff n D P Q hdisc).mpr
      (show lucasUZMod n P Q (lucasProbablePrimeIndex n D) = 0 from
        (lucasProbablePrimeIndex_of_jacobi_eq_neg_one hjacobi).symm ▸
          lucasUZMod_prime_eq_zero n P Q hd)

end PseudoPrime.PrimeTest
