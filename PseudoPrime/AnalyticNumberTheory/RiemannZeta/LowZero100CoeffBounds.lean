/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaFiniteEM8
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100CoeffArithmetic

/-! # Correctness of the rational Euler–Maclaurin correction -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

private theorem endpoint_inv_cast (z : ℚ × ℚ) :
    Analysis.rationalComplexCast (endpointComplexInv z) = (Analysis.rationalComplexCast z)⁻¹ := by
  apply Complex.ext
  · simp only [endpointComplexInv, Analysis.rationalComplexCast, Complex.inv_re,
      Complex.normSq_apply, Rat.cast_div, Rat.cast_add, pow_two, Rat.cast_mul]
  · simp only [endpointComplexInv, Analysis.rationalComplexCast, Complex.inv_im,
      Complex.normSq_apply, Rat.cast_div, Rat.cast_neg, Rat.cast_add, pow_two, Rat.cast_mul]

private theorem endpoint_pair_cast (a b : ℚ) :
    Analysis.rationalComplexCast (a, b) = (a : ℂ) + (b : ℂ) * Complex.I := by
  apply Complex.ext <;>
    simp only [Analysis.rationalComplexCast, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ratCast_re, Complex.ratCast_im, mul_one,
      mul_zero, sub_zero, zero_add, add_zero]

/-- For any rational ordinate, the exact rational correction casts to the grouped analytic
Euler–Maclaurin coefficient. This identifies the endpoint calculation with the approximation
used in the zeta error theorem. -/
theorem endpoint_coefficient_cast (t : ℚ) :
    Analysis.rationalComplexCast (endpointCoefficient t) = finiteEM8Coefficient (t : ℝ) := by
  simp only [endpointCoefficient, Analysis.rationalComplexCast_add,
    Analysis.rationalComplexCast_scale, Analysis.rationalComplexCast_mul, endpoint_inv_cast,
    endpoint_pair_cast]
  simp only [finiteEM8Coefficient, Rat.cast_add, Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat,
    Rat.cast_zero, Rat.cast_one]
  push_cast
  ring

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
