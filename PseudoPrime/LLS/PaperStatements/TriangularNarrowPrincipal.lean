/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.TriangularPrincipalUpperBounds

/-! # Principal comparison for triangular kernels -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- At a positive scale and nonzero index, the principal summand is the von Mangoldt
weight times the triangular profile. The transform formula gives the identity for any
positive width; it is used to compare principal sums of different widths. -/
private theorem term {a x : ℝ} (ha : 0 < a) (hx : 0 < x) {n : ℕ} (hn : n ≠ 0) :
    ((triangularMellinKernel ha).summand (1 : DirichletCharacter ℂ 1) x n).re =
      ArithmeticFunction.vonMangoldt n / Real.sqrt n * triangularKernelProfile a (n / x) := by
  have hp : 0 < (n : ℝ) / x := div_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)) hx
  simp only [MellinKernel.summand, ite_eq_right hn,
    MulChar.one_apply (isUnit_of_subsingleton (n : ZMod 1)), mul_one, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [triangular_transform_of_function _ ha rfl hp]

/-- The width-eight profile is bounded by the width-eighteen profile at the shifted
scale. The triangle inequality supplies the shift used in the principal sum comparison. -/
private theorem prof {u : ℝ} (hu : 0 < u) :
    triangularKernelProfile 8 u ≤ triangularKernelProfile 18 (Real.exp 20 * u) := by
  unfold triangularKernelProfile
  rw [Real.log_mul (Real.exp_pos 20).ne' hu.ne', Real.log_exp]
  apply max_le_max_left
  have h := abs_add_le (20 : ℝ) (Real.log u)
  have ha : |(20 : ℝ)| = 20 := abs_of_nonneg (by norm_num only)
  rw [ha] at h
  linarith only [h]

/-- At positive scale, the width-eight principal sum is at most the width-eighteen
principal sum at scale `exp (-20) * x`. Compare nonnegative summands and sum the
pointwise profile bound; this is the first step toward the middle-range principal budget. -/
theorem triangular8_principal_le_shift {x : ℝ} (hx : 0 < x) :
    (∑' n : ℕ,
          (triangularMellinKernel (by norm_num only : (0 : ℝ) < 8)).summand
            (1 : DirichletCharacter ℂ 1) x n).re ≤
      (∑' n : ℕ,
          (triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)).summand
            (1 : DirichletCharacter ℂ 1) (Real.exp (-20) * x) n).re := by
  have hy : 0 < Real.exp (-20) * x := mul_pos (Real.exp_pos _) hx
  have h8 :=
    Complex.hasSum_re
      (MellinKernel.summable_summand (triangularMellinKernel (by norm_num only : (0 : ℝ) < 8))
          (1 : DirichletCharacter ℂ 1) hx).hasSum
  have h18 :=
    Complex.hasSum_re
      (MellinKernel.summable_summand (triangularMellinKernel (by norm_num only : (0 : ℝ) < 18))
          (1 : DirichletCharacter ℂ 1) hy).hasSum
  rw [← h8.tsum_eq, ← h18.tsum_eq]
  apply Summable.tsum_le_tsum
  · intro n
    by_cases hn : n = 0
    · subst n
      simp only [MellinKernel.summand, ite_true, Complex.zero_re, le_refl]
    · rw [term (by norm_num only) hx hn, term (by norm_num only) hy hn]
      apply mul_le_mul_of_nonneg_left
      · have hu : 0 < (n : ℝ) / x := div_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)) hx
        have h := prof hu
        have he : (n : ℝ) / (Real.exp (-20) * x) = Real.exp 20 * ((n : ℝ) / x) := by
          rw [Real.exp_neg]
          field_simp
        rw [he]
        exact h
      · exact div_nonneg (ArithmeticFunction.vonMangoldt_nonneg) (Real.sqrt_nonneg _)
  · exact h8.summable
  · exact h18.summable

/-- Under RH and at positive scale, bound the width-eight principal sum by the
existing width-eighteen arithmetic estimate at the shifted scale. This transfers the
available principal budget to the narrow kernel needed for the middle range. -/
theorem triangular8_principal_upper (hRH : RiemannHypothesis) {x : ℝ} (hx : 0 < x) :
    (∑' n : ℕ,
          (triangularMellinKernel (by norm_num only : (0 : ℝ) < 8)).summand
            (1 : DirichletCharacter ℂ 1) x n).re ≤
      300000000 * Real.sqrt (Real.exp (-20) * x) +
        1300000 * (Real.exp (-20) * x) ^ (1 / 4 : ℝ) := by
  exact
    (triangular8_principal_le_shift hx).trans
      (triangular18_level_one_arithmetic_upper_of_rh hRH (mul_pos (Real.exp_pos _) hx))

end PseudoPrime.LLS.PaperStatements
