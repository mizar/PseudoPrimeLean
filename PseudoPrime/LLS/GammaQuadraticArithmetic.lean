/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaTruncatedBounds
public import PseudoPrime.LLS.GammaSignedMangoldtCorrection
public import PseudoPrime.NumberTheory.DirichletCharacter

/-! # Quadratic Gamma summands and signed ramp discrepancy -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For a quadratic character, positive scale and nonzero index, the real Gamma
summand equals the character's real value times the normalized exponential Mangoldt weight.
Quadratic values have zero imaginary part; the Gamma transform cancels the square roots. -/
theorem gamma_quadratic_summand_re_eq_exponential {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hquad : χ.IsQuadratic) {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : n ≠ 0) :
    (gammaMellinKernel.summand χ x n).re =
      (χ n).re * Real.exp (-(n : ℝ) / x) * ArithmeticFunction.vonMangoldt n / Real.sqrt x := by
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hu := div_pos hnpos hx
  have him : (χ n).im = 0 := by
    rcases hquad n with hz | h1 | hneg
    · rw [hz]; exact Complex.zero_im
    · rw [h1]; exact Complex.one_im
    · rw [hneg, Complex.neg_im, Complex.one_im, neg_zero]
  simp only [MellinKernel.summand, ite_eq_right hn, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, him, mul_zero, zero_mul, sub_zero, add_zero]
  rw [gamma_transform_of_function gammaMellinKernel rfl hu, Real.sqrt_div hnpos.le, neg_div]
  field_simp (discharger :=
    first
    | exact (Real.sqrt_pos.mpr hnpos).ne'
    | exact (Real.sqrt_pos.mpr hx).ne')

/-- At positive scale, every quadratic Gamma summand has the exponential Mangoldt formula.
Include index zero by Mangoldt vanishing to support whole-series comparisons. -/
theorem gamma_quadratic_summand_re_eq_exponential_all {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hquad : χ.IsQuadratic) {x : ℝ} (hx : 0 < x) (n : ℕ) :
    (gammaMellinKernel.summand χ x n).re =
      (χ n).re * Real.exp (-(n : ℝ) / x) * ArithmeticFunction.vonMangoldt n / Real.sqrt x := by
  by_cases hn : n = 0
  · have hz : ArithmeticFunction.vonMangoldt 0 = 0 :=
      ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr not_isPrimePow_zero
    simp only [hn, MellinKernel.summand, ite_true, Complex.zero_re, hz, mul_zero, zero_div]
  · exact gamma_quadratic_summand_re_eq_exponential χ hquad hx hn

/-- The level-one and primitive Gamma summands plus the signed ramp discrepancy
equal twice the normalized ramp Mangoldt term at every index.
Expand the exact exponential formulas and keep the correction's sign.
This identifies the arithmetic terms in the no-witness comparison. -/
theorem gamma_pair_summand_add_signed_term {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hquad : χ.IsQuadratic) {x : ℝ} (hx : 0 < x) (n : ℕ) :
    (gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x n).re +
        (gammaMellinKernel.summand χ.primitiveCharacter x n).re +
        (ArithmeticFunction.vonMangoldt n / Real.sqrt x *
          Analysis.exponentialRampLocalCorrection (χ.primitiveCharacter n) ((n : ℝ) / x) 1) =
      2 *
        (ArithmeticFunction.vonMangoldt n * Analysis.exponentialRampWeight ((n : ℝ) / x) /
          Real.sqrt x) := by
  have h1 : (1 : DirichletCharacter ℂ 1).IsQuadratic := fun z ↦
    Or.inr (Or.inl (MulChar.one_apply (isUnit_of_subsingleton z)))
  rw [gamma_quadratic_summand_re_eq_exponential_all _ h1 hx,
    gamma_quadratic_summand_re_eq_exponential_all _
      (NumberTheory.isQuadratic_primitiveCharacter χ hquad) hx]
  simp only [Analysis.exponentialRampLocalCorrection, pow_one, Complex.add_re, Complex.one_re,
    MulChar.one_apply (isUnit_of_subsingleton (n : ZMod 1)), neg_div]
  ring

end PseudoPrime.LLS.PaperStatements
