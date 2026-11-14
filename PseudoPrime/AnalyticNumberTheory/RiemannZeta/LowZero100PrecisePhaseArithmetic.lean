/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100PreciseFiniteArithmetic
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100PhaseArithmetic

/-! # High-precision rational phase for low-zero endpoints -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Round `t/(2*endpointPi)` to a grid of width `10⁻¹²`, retaining enough precision for
the common endpoint margin. -/
def endpointPreciseArgument (t : ℚ) : ℚ :=
  Analysis.rationalGridFloor (10 ^ 12) (t / (2 * endpointPi))

/-- Compute a precise rational logarithm of the rounded phase argument using the internally
certified narrow interval for `log 2` and 64 Taylor terms. -/
def endpointPrecisePhaseLog (t : ℚ) : ℚ :=
  let q := endpointPreciseArgument t
  Analysis.rationalGridFloor (10 ^ 12)
    (Analysis.rationalPreciseLogUpper q (endpointPhaseScale q) 64)

/-- Check the phase argument range and an exact rational interval of radius `10⁻¹¹` around
the computed phase logarithm. -/
def endpointPrecisePhaseCheck (t : ℚ) : Bool :=
  let q := endpointPreciseArgument t
  decide (2 ≤ q ∧ q ≤ 16) &&
    Analysis.rationalPreciseLogCheck q (endpointPhaseScale q) 64
      (endpointPrecisePhaseLog t - 1 / 100000000000) (endpointPrecisePhaseLog t + 1 / 100000000000)

/-- Compute a high-precision rational approximation to the elementary phase from the
rounded logarithm and rational pi input. -/
def endpointPreciseTheta (t : ℚ) : ℚ :=
  t / 2 * endpointPrecisePhaseLog t - t / 2 - endpointPi / 8

/-- Compute the high-precision finite Euler–Maclaurin approximation after rational phase
rotation. Its real component is used in the endpoint sign certificates. -/
def endpointPreciseRotated (t : ℚ) : ℚ × ℚ :=
  Analysis.rationalComplexMul
    (Analysis.rationalScaledPhase (10 ^ 15) (endpointPreciseTheta t) 16 11)
    (endpointPreciseFinite t)

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
