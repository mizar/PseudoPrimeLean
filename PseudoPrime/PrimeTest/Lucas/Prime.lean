import PseudoPrime.PrimeTest.Lucas.FiniteField

/-! # Prime completeness of the Lucas U test in the Jacobi minus-one branch -/

namespace PseudoPrime.PrimeTest

/-- With the discriminant identity and Jacobi value -1, every prime passes the Lucas U test.
The finite-field bridge gives U at n+1; the index theorem identifies the executable index.
Other Jacobi branches are not covered by this theorem. -/
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
