/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ExponentialRampNormBounds
public import PseudoPrime.LLS.GammaQuadraticNoWitness

/-! # Gamma ramp no-witness comparison for general complex characters -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For any complex Dirichlet character at positive scale and nonzero index, the
real Gamma summand is the real character value times the normalized exponential
Mangoldt term. Use the real Mellin transform, rather than assuming a real character.
This extends the arithmetic identity to characters used in MR subgroup bounds. -/
theorem gamma_summand_re_eq_exponential {q : ℕ} (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 0 < x)
    {n : ℕ} (hn : n ≠ 0) :
    (gammaMellinKernel.summand χ x n).re =
      (χ n).re * Real.exp (-(n : ℝ) / x) * ArithmeticFunction.vonMangoldt n / Real.sqrt x := by
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hu := div_pos hnpos hx
  have him : (gammaMellinKernel.transform ((n : ℝ) / x)).im = 0 :=
    gammaMellinKernel.mellin_real _ hu
  simp only [MellinKernel.summand, ite_eq_right hn, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, him, mul_zero, zero_mul, sub_zero, add_zero]
  rw [gamma_transform_of_function gammaMellinKernel rfl hu, Real.sqrt_div hnpos.le, neg_div]
  field_simp (discharger :=
    first
    | exact (Real.sqrt_pos.mpr hnpos).ne'
    | exact (Real.sqrt_pos.mpr hx).ne')

/-- For any complex character, include index zero in the exact real Gamma-summand
formula. Mangoldt vanishing handles zero. This supports whole-series comparisons. -/
theorem gamma_summand_re_eq_exponential_all {q : ℕ} (χ : DirichletCharacter ℂ q) {x : ℝ}
    (hx : 0 < x) (n : ℕ) :
    (gammaMellinKernel.summand χ x n).re =
      (χ n).re * Real.exp (-(n : ℝ) / x) * ArithmeticFunction.vonMangoldt n / Real.sqrt x := by
  by_cases hn : n = 0
  · have hz : ArithmeticFunction.vonMangoldt 0 = 0 :=
      ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr not_isPrimePow_zero
    simp only [hn, MellinKernel.summand, ite_true, Complex.zero_re, hz, mul_zero, zero_div]
  · exact gamma_summand_re_eq_exponential χ hx hn

end PseudoPrime.LLS.PaperStatements

namespace PseudoPrime.LLS.PaperStatements

/-- For every complex character and positive scale, the principal and primitive
Gamma summands plus their signed discrepancy equal twice the ramp term.
Expand the real-transform formulas and preserve signs. This is the pointwise
identity behind general-character witness extraction. -/
theorem gamma_pair_summand_add_signed_term_general {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x : ℝ} (hx : 0 < x) (n : ℕ) :
    (gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x n).re +
        (gammaMellinKernel.summand χ.primitiveCharacter x n).re +
        (ArithmeticFunction.vonMangoldt n / Real.sqrt x *
          Analysis.exponentialRampLocalCorrection (χ.primitiveCharacter n) ((n : ℝ) / x) 1) =
      2 *
        (ArithmeticFunction.vonMangoldt n * Analysis.exponentialRampWeight ((n : ℝ) / x) /
          Real.sqrt x) := by
  rw [gamma_summand_re_eq_exponential_all _ hx, gamma_summand_re_eq_exponential_all _ hx]
  simp only [Analysis.exponentialRampLocalCorrection, pow_one, Complex.add_re, Complex.one_re,
    MulChar.one_apply (isUnit_of_subsingleton (n : ZMod 1)), neg_div]
  ring

end PseudoPrime.LLS.PaperStatements
