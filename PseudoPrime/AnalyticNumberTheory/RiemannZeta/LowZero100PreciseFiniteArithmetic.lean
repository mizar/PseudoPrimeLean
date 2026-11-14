/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100CoeffArithmetic
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100PowerArithmetic
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100PreciseLogArithmetic

/-! # Precise rational finite Euler–Maclaurin approximation -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Compute a half-open block of rational power terms using the precise shared logarithms.
Small blocks let the endpoint checks verify a large finite sum in separate reductions. -/
def endpointPreciseBlock (t : ℚ) (a b : ℕ) : ℚ × ℚ :=
  ∑ n ∈ Finset.Ico a b, endpointPowerApprox t (endpointPreciseLog n)

/-- Compute the exact correction coefficient times the rounded 128th power obtained from
the precise logarithm. It is checked separately from the ordinary finite-sum blocks. -/
def endpointPreciseCorrection (t : ℚ) : ℚ × ℚ :=
  Analysis.rationalComplexMul (endpointCoefficient t)
    (endpointPowerApprox t (endpointPreciseLog 128))

/-- Compute the 127 rational power terms and the grouped correction using the precise
shared logarithms. A separate theorem bounds the difference from the analytic approximation. -/
def endpointPreciseFinite (t : ℚ) : ℚ × ℚ :=
  Analysis.rationalComplexAdd
    (∑ n ∈ Finset.Icc (1 : ℕ) 127, endpointPowerApprox t (endpointPreciseLog n))
    (endpointPreciseCorrection t)

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
