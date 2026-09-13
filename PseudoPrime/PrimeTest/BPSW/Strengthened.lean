/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import PseudoPrime.PrimeTest.BPSW.Prime
import PseudoPrime.PrimeTest.EulerJacobi.Prime
import PseudoPrime.PrimeTest.LucasV.Prime

/-!
# Strengthened parameterized Baillie–PSW composition

The strengthened interface adds the Lucas-V and Euler–Jacobi tests with the
Lucas base `Q` to the explicit-parameter Baillie–PSW composition.
-/

namespace PseudoPrime.PrimeTest

/-- Baillie–PSW with explicit Lucas parameters and the Euler–Jacobi check. -/
def strengthenedBPSWWithParams (n : ℕ) (D P Q : ℤ) : Bool :=
  bailliePSWWithParams n D P Q && (lucasVWithParams n D P Q && eulerJacobiWithIntBase n Q)

/-- A prime modulus passes the strengthened parameterized Baillie–PSW composition. -/
theorem strengthenedBPSWWithParams_of_prime {n : ℕ} (hn : n.Prime) (D P Q : ℤ)
    (hdisc : D = P * P - 4 * Q) (hjacobi : jacobiSym D n = -1) :
    strengthenedBPSWWithParams n D P Q = true := by
  rw [strengthenedBPSWWithParams, Bool.and_eq_true]
  constructor
  · exact bailliePSWWithParams_of_prime hn D P Q hdisc hjacobi
  · rw [Bool.and_eq_true]
    exact ⟨lucasVWithParams_of_prime hn D P Q hdisc hjacobi, eulerJacobiWithIntBase_of_prime hn Q⟩

end PseudoPrime.PrimeTest
