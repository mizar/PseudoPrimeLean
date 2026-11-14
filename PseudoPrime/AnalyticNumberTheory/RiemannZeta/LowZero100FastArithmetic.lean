/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.RationalHorner16
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100CachedArithmetic

/-! # Horner-based finite evaluation at low-zero endpoints -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Compute the rounded complex power from rational `t` and logarithm `q`, using a
16-term Horner polynomial for each exponential and the same rounded-squaring grids. -/
def endpointFastPower (t q : ℚ) : ℚ × ℚ :=
  Analysis.rationalComplexMul (Analysis.rationalHornerRealExp16 (10 ^ 15) (-(1 / 2 : ℚ) * q) 6)
    (Analysis.rationalHornerPhase16 (10 ^ 15) (-t * q) 11)

/-- Compute the 127 power terms and grouped correction using cached logarithms and the
Horner power evaluator. It is equal to the previously certified finite approximation. -/
def endpointFastFinite (t : ℚ) : ℚ × ℚ :=
  Analysis.rationalComplexAdd
    (∑ n ∈ Finset.Icc (1 : ℕ) 127, endpointFastPower t (endpointCachedLog n))
    (Analysis.rationalComplexMul (endpointCoefficient t)
      (endpointFastPower t (endpointCachedLog 128)))

/-- Compute the rotated rational finite approximation using Horner evaluation and cached
logarithms. Its real component is the input to the endpoint certificates. -/
def endpointFastRotated (t : ℚ) : ℚ × ℚ :=
  Analysis.rationalComplexMul (Analysis.rationalHornerPhase16 (10 ^ 15) (endpointPreciseTheta t) 11)
    (endpointFastFinite t)

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
