/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100CoeffArithmetic
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100PowerArithmetic
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridLogArithmetic

/-! # Rational finite Euler–Maclaurin approximation -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Compute a half-open block of rounded rational power terms at a rational ordinate.
Small blocks let kernel checks certify a large finite sum without one large reduction. -/
def endpointFiniteBlock (t : ℚ) (a b : ℕ) : ℚ × ℚ :=
  ∑ n ∈ Finset.Ico a b, endpointPowerApprox t (gridLogApprox n)

/-- Compute the exact correction coefficient multiplied by the rounded power at 128.
It is kept separate from the blocks of ordinary terms for endpoint certificates. -/
def endpointFiniteCorrection (t : ℚ) : ℚ × ℚ :=
  Analysis.rationalComplexMul (endpointCoefficient t) (endpointPowerApprox t (gridLogApprox 128))

/-- Compute the 127 rounded power terms and exact grouped correction for a rational ordinate.
The output is a rational complex pair; its error is proved separately using the term bounds. -/
def endpointFiniteApprox (t : ℚ) : ℚ × ℚ :=
  Analysis.rationalComplexAdd
    (∑ n ∈ Finset.Icc (1 : ℕ) 127, endpointPowerApprox t (gridLogApprox n))
    (endpointFiniteCorrection t)

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
