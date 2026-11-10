/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterScaleOneAbel

/-! # Joint Abel summation inside triangular support -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A principal summand at a positive interior scale and below that scale has
the stated logarithmic triangular weight. Evaluate the transform and profile;
this supplies the finite joint Abel identity. -/
theorem quarter_interior_term {a X : ℝ} (ha : 0 < a) (hX : 1 ≤ X) (hbound : Real.log X ≤ 2 * a)
    {n : ℕ} (hn : 1 ≤ n) (hnX : (n : ℝ) ≤ X) :
    ((LLS.PaperStatements.triangularMellinKernel ha).summand (1 : DirichletCharacter ℂ 1) X n).re =
      ((2 * a - Real.log X + Real.log n) * (n : ℝ) ^ (-1 / 2 : ℝ)) *
        ArithmeticFunction.vonMangoldt n := by
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hlog0 := Real.log_nonneg hn1
  have hlog := Real.log_le_log hnpos hnX
  have hprof :
    LLS.PaperStatements.triangularKernelProfile a ((n : ℝ) / X) =
      2 * a - Real.log X + Real.log n := by
    unfold LLS.PaperStatements.triangularKernelProfile
    rw [Real.log_div hnpos.ne' hXp.ne', abs_of_nonpos (by linarith only [hlog])]
    rw [max_eq_right (by linarith only [hlog0, hbound])]
    ring
  simp only [LLS.PaperStatements.MellinKernel.summand, ite_eq_right hn0,
    MulChar.one_apply (isUnit_of_subsingleton (n : ZMod 1)), mul_one, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [LLS.PaperStatements.triangular_transform_of_function _ ha rfl (div_pos hnpos hXp), hprof,
    neg_div, Real.rpow_neg hnpos.le, ← Real.sqrt_eq_rpow]
  ring

/-- For an interior triangular scale, express the finite forward sum and
twice the finite scale-one sum by one Chebyshev boundary term and one Abel
integral. Combine the two explicit weights before applying Abel summation. -/
theorem quarter_interior_abel {a X : ℝ} (ha : 0 < a) (hX : 1 ≤ X) (hbound : Real.log X ≤ 2 * a) :
    (∑ n ∈ Finset.Icc 1 ⌊X⌋₊,
          ((LLS.PaperStatements.triangularMellinKernel ha).summand (1 : DirichletCharacter ℂ 1) X
              n).re) +
        2 *
          (∑ n ∈ Finset.Icc 1 ⌊X⌋₊,
            ((LLS.PaperStatements.triangularMellinKernel ha).summand (1 : DirichletCharacter ℂ 1) 1
                n).re) =
      ((6 * a - 2 * Real.log X) * X ^ (-1 / 2 : ℝ)) * Chebyshev.psi X +
        ∫ t in Set.Ioc 1 X,
          (t ^ (-3 / 2 : ℝ) * (3 * a - Real.log X / 2 + 1 - Real.log t / 2)) * Chebyshev.psi t := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  have hfinite :
    (∑ n ∈ Finset.Icc 1 ⌊X⌋₊,
        (((LLS.PaperStatements.triangularMellinKernel ha).summand (1 : DirichletCharacter ℂ 1) X
              n).re +
          2 *
            ((LLS.PaperStatements.triangularMellinKernel ha).summand (1 : DirichletCharacter ℂ 1) 1
                n).re)) =
      ∑ n ∈ Finset.Icc 1 ⌊X⌋₊,
        ((2 * (3 * a - Real.log X / 2) - Real.log n) * (n : ℝ) ^ (-1 / 2 : ℝ)) *
          ArithmeticFunction.vonMangoldt n := by
    apply Finset.sum_congr rfl
    intro n hn
    have hn' := Finset.mem_Icc.mp hn
    have hnX : (n : ℝ) ≤ X := (Nat.cast_le.mpr hn'.2).trans (Nat.floor_le (zero_le_one.trans hX))
    rw [quarter_interior_term ha hX hbound hn'.1 hnX, quarter_scale_one_term ha hbound hn'.1 hnX]
    ring
  rw [hfinite]
  have hfloor : 1 ≤ ⌊X⌋₊ := Nat.le_floor (by exact_mod_cast hX)
  rw [Finset.Icc_eq_cons_Ioc hfloor, Finset.sum_cons]
  simp only [Nat.cast_one, ArithmeticFunction.vonMangoldt_apply_one, mul_zero, zero_add]
  have h :=
    quarter_scale_one_mangoldt_abel (a := 3 * a - Real.log X / 2) (u := 1) (v := X)
      (by norm_num only) hX
  simp only [Nat.floor_one, Chebyshev.psi_one, mul_zero, sub_zero] at h
  have heq :
    (fun t : ℝ ↦
        (t ^ (-3 / 2 : ℝ) * (Real.log t / 2 - (3 * a - Real.log X / 2) - 1)) * Chebyshev.psi t) =
      fun t ↦
      -((t ^ (-3 / 2 : ℝ) * (3 * a - Real.log X / 2 + 1 - Real.log t / 2)) * Chebyshev.psi t) := by
    funext t
    ring
  rw [heq, MeasureTheory.integral_neg] at h
  convert h using 1
  ring_nf

end PseudoPrime.PrimeTestBounds.MillerRabin
