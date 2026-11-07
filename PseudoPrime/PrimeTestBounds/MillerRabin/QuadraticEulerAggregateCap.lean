/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerRowCap0
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerRowCap250
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerRowCap500
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerRowCap750
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerRowCap1000
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerRowCap1250
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerRowCap1500
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerRowCap1750
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerRowCap2000
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerRowCap2250
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerRowCap2500
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerRowCap2750
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerRowCap3000
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerRowCap3250
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerRowCap3500
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerRowCap3750
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerRowCap4000
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerRowCap4250
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerRowCap4500
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerRowCap4750
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerRowCap5000

/-! # Certified scalar upper bound for all Euler-center rows -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Sum of the independently certified block caps. It is a rational number
so the following comparison is checked by kernel arithmetic. -/
def centerRows50000Upper : ℚ :=
  centerRows0Upper + centerRows250Upper + centerRows500Upper + centerRows750Upper +
    centerRows1000Upper +
    centerRows1250Upper +
    centerRows1500Upper +
    centerRows1750Upper +
    centerRows2000Upper +
    centerRows2250Upper +
    centerRows2500Upper +
    centerRows2750Upper +
    centerRows3000Upper +
    centerRows3250Upper +
    centerRows3500Upper +
    centerRows3750Upper +
    centerRows4000Upper +
    centerRows4250Upper +
    centerRows4500Upper +
    centerRows4750Upper +
    centerRows5000Upper

/-- The total of all outward-rounded block caps is at most 5.805279.
This exact scalar bound is used for the actual finite Euler prefix. -/
theorem centerRows50000_upper_check : centerRows50000Upper ≤ 5805279 / 1000000 := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
