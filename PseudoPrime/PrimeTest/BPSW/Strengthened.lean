/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.BPSW.Prime
public import PseudoPrime.PrimeTest.EulerJacobi.Prime
public import PseudoPrime.PrimeTest.LucasV.Prime

/-!
# Strengthened parameterized Baillie–PSW composition

The strengthened interface adds the Lucas-V and Euler–Jacobi tests with the
Lucas base `Q` to the explicit-parameter Baillie–PSW composition.
-/

@[expose] public section

namespace PseudoPrime.PrimeTest

/--
Parameterized conjunction of ordinary BPSW, Lucas-V, and signed Euler–Jacobi at base `Q`.
The input is natural `n` and the parameters `D`, `P`, `Q` are integers. Require all three
Boolean comparisons to accept; parameter search is not performed here. This uses the raw
unmultiplied Euler comparison with exponent `n / 2`, distinct from the later Wheel30 shared
implementation until its equivalence hypotheses are discharged.
-/
def strengthenedBPSWWithParams (n : ℕ) (D P Q : ℤ) : Bool :=
  bailliePSWWithParams n D P Q && (lucasVWithParams n D P Q && eulerJacobiWithIntBase n Q)

/--
A prime passes all three parameterized strengthened BPSW comparisons.
The premises are `n.Prime`, `D = P * P - 4 * Q`, and `jacobiSym D n = -1`.
The proof splits the conjunction and combines ordinary BPSW, Lucas-V, and signed Euler–Jacobi
prime-pass theorems. No further coprimality hypothesis on `Q` is imposed.
This supplies the parameter-level strengthened prime-completeness contract.
-/
theorem strengthenedBPSWWithParams_of_prime {n : ℕ} (hn : n.Prime) (D P Q : ℤ)
    (hdisc : D = P * P - 4 * Q) (hjacobi : jacobiSym D n = -1) :
    strengthenedBPSWWithParams n D P Q = true := by
  rw [strengthenedBPSWWithParams, Bool.and_eq_true]
  constructor
  · exact bailliePSWWithParams_of_prime hn D P Q hdisc hjacobi
  · rw [Bool.and_eq_true]
    exact ⟨lucasVWithParams_of_prime hn D P Q hdisc hjacobi, eulerJacobiWithIntBase_of_prime hn Q⟩

end PseudoPrime.PrimeTest
