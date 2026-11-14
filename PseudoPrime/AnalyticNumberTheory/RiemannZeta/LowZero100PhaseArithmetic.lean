/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100FiniteArithmetic

/-! # Rational phase evaluator for low-zero endpoints -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- A rational approximation to pi used only as an input to the finite phase evaluator.
Its difference from pi is bounded separately by an internal analytic theorem. -/
def endpointPi : ℚ :=
  3141592653589793 / 10 ^ 15

/-- Round `t / (2 * endpointPi)` down to a fixed decimal grid before computing logarithms.
This limits denominator growth in the subsequent rational Taylor calculation. -/
def endpointPhaseArgument (t : ℚ) : ℚ :=
  Analysis.rationalGridFloor (10 ^ 9) (t / (2 * endpointPi))

/-- Select a nearby power of two for the logarithmic Taylor series of the phase argument.
The three branches cover all endpoint arguments from 14 to 100. -/
def endpointPhaseScale (q : ℚ) : ℕ :=
  if q ≤ 4 then 2 else if q ≤ 8 then 3 else 4

/-- Compute a rounded logarithm of the rational phase argument with 32 Taylor terms.
Its accuracy is verified independently for the endpoint inputs. -/
def endpointPhaseLog (t : ℚ) : ℚ :=
  let q := endpointPhaseArgument t
  Analysis.rationalGridFloor (10 ^ 9) (Analysis.rationalLogUpper q (endpointPhaseScale q) 32)

/-- Check the logarithm input range and a two-sided rational enclosure around the computed
phase logarithm. The Boolean check is evaluated independently for each required endpoint. -/
def endpointPhaseLogCheck (t : ℚ) : Bool :=
  let q := endpointPhaseArgument t
  decide (2 ≤ q ∧ q ≤ 16) &&
    Analysis.rationalLogIntervalCheck q (endpointPhaseScale q) 32
      (endpointPhaseLog t - 1 / 100000000) (endpointPhaseLog t + 1 / 100000000)

/-- Compute the rational approximation to the elementary phase
`(t/2) * log(t/(2*pi)) - t/2 - pi/8`. -/
def endpointTheta (t : ℚ) : ℚ :=
  t / 2 * endpointPhaseLog t - t / 2 - endpointPi / 8

/-- Compute the phase-rotated finite zeta approximation as a rational complex pair.
The real component supplies the endpoint sign certificate. -/
def endpointRotatedFinite (t : ℚ) : ℚ × ℚ :=
  Analysis.rationalComplexMul (Analysis.rationalScaledPhase (10 ^ 15) (endpointTheta t) 16 11)
    (endpointFiniteApprox t)

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
