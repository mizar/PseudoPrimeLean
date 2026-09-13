import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LeftVerticalLBound
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.QuadraticFunctionalConsequences

/-! Kernel-independent estimates extracted from the contour applications. -/

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/--
Input/assumptions: `χ` primitive nontrivial quadratic mod `N`, `A : ℕ` with `2 ≤ A`, `t : ℝ`.
Conclusion: `LFunction χ (s_A(t)) ≠ 0`, where `s_A(t) := -A - 1/2 + t i`.
Content: `(1 - s_A(t)).re = A + 3/2 ≥ 1` supplies
`completedLFunction_ne_zero_farLeft_of_isQuadratic` (completed `L` is nonzero at `s_A(t)` itself);
parity dispatch on `χ` supplies `gammaFactor χ (s_A(t)) ≠ 0` via the pole-avoidance facts
`leftVertical_even/odd_half_ne_neg_nat`; `L = completedL / gammaFactor`
(`DirichletLFunction.dirichletLFunction_eq_completed_div_gammaFactor`) then gives `L (s_A(t)) ≠ 0`
as a quotient of two
nonzero numbers. (`A ≥ 2` is not actually needed here, kept only for signature uniformity with the
sibling left-vertical theorems.)
Role: supplies the differentiability/continuity input needed for the kernel's measurability on the
left-vertical line.
-/
theorem quadraticDirichletLFunction_ne_zero_leftVertical {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hquad : χ.IsQuadratic)
    (A : ℕ) (_hA : 2 ≤ A) (t : ℝ) :
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
    rw [h1, hsre]; linarith
  have hFsne :=
    completedLFunction_ne_zero_farLeft_of_isQuadratic
      hprimitive hne hquad hs1re
  have hΓsne : DirichletCharacter.gammaFactor χ s ≠ 0 := by
    rcases χ.even_or_odd with heven | hodd
    · exact
        gammaFactor_ne_zero_of_even_of_half_ne_neg_nat
          heven
          (leftVertical_even_half_ne_neg_nat A
            t)
    · exact
        gammaFactor_ne_zero_of_odd_of_half_ne_neg_nat
          hodd
          (leftVertical_odd_half_ne_neg_nat A t)
  have hLeq :=
    dirichletLFunction_eq_completed_div_gammaFactor
      χ s
      (Or.inr
        (dirichletCharacter_level_ne_one_of_ne_one
          hne))
  rw [hLeq]
  exact div_ne_zero hFsne hΓsne

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
    linarith
  have hFsne :=
    completedLFunction_ne_zero_farLeft
      hprimitive hne hinv hs1re
  have hΓsne : DirichletCharacter.gammaFactor χ s ≠ 0 := by
    rcases χ.even_or_odd with heven | hodd
    · exact
        gammaFactor_ne_zero_of_even_of_half_ne_neg_nat
          heven
          (leftVertical_even_half_ne_neg_nat A
            t)
    · exact
        gammaFactor_ne_zero_of_odd_of_half_ne_neg_nat
          hodd
          (leftVertical_odd_half_ne_neg_nat A t)
  have hLeq :=
    dirichletLFunction_eq_completed_div_gammaFactor
      χ s
      (Or.inr
        (dirichletCharacter_level_ne_one_of_ne_one
          hne))
  rw [hLeq]
  exact div_ne_zero hFsne hΓsne

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
