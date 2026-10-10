/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LeftVerticalLBound
public import Mathlib.NumberTheory.MulChar.Basic
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.Basic
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveFunctionalEquation

/-! Kernel-independent estimates extracted from the contour applications. -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- Generic left-vertical nonvanishing, using the inverse-character far-left reflection. -/
theorem dirichletLFunction_ne_zero_leftVertical {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (A : ℕ) (hA : 2 ≤ A) (t : ℝ) :
    DirichletCharacter.LFunction χ (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
  set s : ℂ := ((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I with hs_def
  have hsre : s.re = -(A : ℝ) - 1 / 2 := by
    simp only [hs_def, one_div, Complex.ofReal_sub, Complex.ofReal_neg, Complex.ofReal_natCast,
      Complex.ofReal_inv, Complex.ofReal_ofNat, Complex.add_re, Complex.sub_re, Complex.neg_re,
      Complex.natCast_re, Complex.inv_re, Complex.re_ofNat, Complex.normSq_ofNat,
      div_self_mul_self', Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
  have hs1re : (1 : ℝ) ≤ (1 - s).re := by
    have h1 : (1 - s).re = 1 - s.re := by simp only [Complex.sub_re, Complex.one_re]
    rw [h1, hsre]
    have hA' : (2 : ℝ) ≤ A := by exact_mod_cast hA
    linarith only [hA']
  have hFsne := completedLFunction_ne_zero_farLeft hprimitive hne hinv hs1re
  have hΓsne : DirichletCharacter.gammaFactor χ s ≠ 0 := by
    rcases χ.even_or_odd with heven | hodd
    · exact
        gammaFactor_ne_zero_of_even_of_half_ne_neg_nat heven (leftVertical_even_half_ne_neg_nat A t)
    · exact
        gammaFactor_ne_zero_of_odd_of_half_ne_neg_nat hodd (leftVertical_odd_half_ne_neg_nat A t)
  have hLeq :=
    dirichletLFunction_eq_completed_div_gammaFactor χ s
      (Or.inr (dirichletCharacter_level_ne_one_of_ne_one hne))
  rw [hLeq]
  exact div_ne_zero hFsne hΓsne

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
