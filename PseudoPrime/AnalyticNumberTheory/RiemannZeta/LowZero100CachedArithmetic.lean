/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100CachedLogs
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100PrecisePhaseArithmetic

/-! # Cached finite evaluation at low-zero endpoints -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Compute the rational finite Euler–Maclaurin approximation using cached logarithms.
Separate kernel proofs identify every cached logarithm with its precise Taylor calculation. -/
def endpointCachedFinite (t : ℚ) : ℚ × ℚ :=
  Analysis.rationalComplexAdd
    (∑ n ∈ Finset.Icc (1 : ℕ) 127, endpointPowerApprox t (endpointCachedLog n))
    (Analysis.rationalComplexMul (endpointCoefficient t)
      (endpointPowerApprox t (endpointCachedLog 128)))

/-- Compute the rational phase-rotated finite approximation using the verified cached
logarithms. Endpoint certificates check its real component using exact rational arithmetic. -/
def endpointCachedRotated (t : ℚ) : ℚ × ℚ :=
  Analysis.rationalComplexMul
    (Analysis.rationalScaledPhase (10 ^ 15) (endpointPreciseTheta t) 16 11) (endpointCachedFinite t)

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
