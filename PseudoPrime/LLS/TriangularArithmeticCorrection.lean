/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TriangularPrincipalCutoff
public import PseudoPrime.LLS.MellinKernelPrimitiveComparison

/-! # Explicit alpha-18 arithmetic correction majorants -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- The alpha-18 inverse transform has norm at most 36 at positive arguments.
Apply the general mass bound and the exact triangular mass. -/
theorem triangular18_transform_norm_le {u : ℝ} (hu : 0 < u) :
    ‖(triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)).transform u‖ ≤ 36 := by
  have h :=
    MellinKernel.norm_transform_le_mass (triangularMellinKernel (by norm_num only : (0 : ℝ) < 18))
      hu
  rw [triangular_mass_of_function _ (by norm_num only : (0 : ℝ) < 18) rfl] at h
  norm_num only at h
  exact h

/-- For any character and positive scale, a nonzero arithmetic term has norm
at most 36 Lambda(n)/sqrt n. Combine character norm and transform bounds. -/
theorem triangular18_summand_norm_le {q n : ℕ} (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 0 < x)
    (hn : n ≠ 0) :
    ‖(triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)).summand χ x n‖ ≤
      36 * (ArithmeticFunction.vonMangoldt n / Real.sqrt n) := by
  have ha : 0 ≤ ArithmeticFunction.vonMangoldt n / Real.sqrt n :=
    div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
  have hu : 0 < (n : ℝ) / x := div_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)) hx
  rw [MellinKernel.summand, ite_eq_right hn, norm_mul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg ha]
  have hχ := mul_le_mul_of_nonneg_left (χ.norm_le_one (n : ZMod q)) ha
  have ht :=
    mul_le_mul hχ (triangular18_transform_norm_le hu) (norm_nonneg _) (mul_nonneg ha zero_le_one)
  simpa only [mul_one, one_mul, mul_comm] using ht

/-- The primitive level-change correction vanishes on quotient units;
otherwise its norm is at most 36 Lambda(n)/sqrt n at positive scale.
Use the primitive support identity without losing a factor of two. -/
theorem triangular18_primitive_correction_term_le {q n : ℕ} (χ : DirichletCharacter ℂ q) {x : ℝ}
    (hx : 0 < x) :
    ‖(triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)).summand χ x n -
          (triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)).summand χ.primitiveCharacter x
            n‖ ≤
      if Nat.Coprime n (q / χ.conductor) then 0
      else 36 * (ArithmeticFunction.vonMangoldt n / Real.sqrt n) := by
  let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
  by_cases hc : Nat.Coprime n (q / χ.conductor)
  · rw [ite_eq_left hc, MellinKernel.summand_eq_primitive_of_coprime_quotient K χ x hc, sub_self,
      norm_zero]
  · rw [ite_eq_right hc]
    by_cases hn : n = 0
    · subst n
      simp only [MellinKernel.summand, ite_true, sub_self, norm_zero]
      exact
        mul_nonneg (by norm_num only)
          (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))
    · exact
        (MellinKernel.norm_summand_sub_primitive_le K χ x).trans
          (triangular18_summand_norm_le χ.primitiveCharacter hx hn)

/-- At positive scale, the norm of any finite primitive correction sum is
bounded by the explicit Mangoldt majorant restricted to quotient nonunits.
Sum the termwise bounds; prime-power estimates can further reduce this budget. -/
theorem triangular18_primitive_correction_sum_le {q : ℕ} (χ : DirichletCharacter ℂ q) {x : ℝ}
    (hx : 0 < x) (s : Finset ℕ) :
    ‖∑ n ∈ s,
          ((triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)).summand χ x n -
            (triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)).summand χ.primitiveCharacter
              x n)‖ ≤
      ∑ n ∈ s,
        if Nat.Coprime n (q / χ.conductor) then 0
        else 36 * (ArithmeticFunction.vonMangoldt n / Real.sqrt n) := by
  exact
    (norm_sum_le _ _).trans
      (Finset.sum_le_sum (fun n _ ↦ triangular18_primitive_correction_term_le χ hx))

end PseudoPrime.LLS.PaperStatements
