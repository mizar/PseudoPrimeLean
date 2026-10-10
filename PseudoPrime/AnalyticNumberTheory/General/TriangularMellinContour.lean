/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.General.TriangularMellinInversion
public import PseudoPrime.AnalyticNumberTheory.RectangleGeometry.VerticalLimits
public import PseudoPrime.Analysis.TriangularMellinBounds

/-! # Integration-line independence for the triangular Mellin kernel

Quadratic strip decay removes the horizontal sides of Cauchy rectangles.
The resulting vertical-line equality supplies the admissibility condition
needed by the triangular kernel in Section 6.2.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.General

/-- For a positive parameter and argument, triangular inverse-Mellin integrals
agree on any two lines of real coordinate in the closed unit interval.
The power factor preserves strip decay up to a constant; Cauchy's theorem
and absolute convergence then identify the vertical integrals. This removes
the line-independence assumption from the concrete triangular kernel. -/
theorem integral_triangular_vertical_eq {a c d u : ℝ} (ha : 0 < a) (hu : 0 < u) (hc : |c| ≤ 1)
    (hd : |d| ≤ 1) :
    (∫ t : ℝ,
        Analysis.triangularMellinFunction a ((c : ℂ) + Complex.I * t) *
          (u : ℂ) ^ (-((c : ℂ) + Complex.I * t))) =
      (∫ t : ℝ,
        Analysis.triangularMellinFunction a ((d : ℂ) + Complex.I * t) *
          (u : ℂ) ^ (-((d : ℂ) + Complex.I * t))) := by
  let f : ℂ → ℂ := fun s ↦ Analysis.triangularMellinFunction a s * (u : ℂ) ^ (-s)
  have hf : Differentiable ℂ f :=
    (Analysis.differentiable_triangularMellinFunction a).mul
      (differentiable_id.neg.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hu.ne')))
  obtain ⟨C, hC, hb⟩ := Analysis.triangularMellinFunction_strip_bound ha
  have hpow (s : ℂ) (hs : |s.re| ≤ 1) : ‖(u : ℂ) ^ (-s)‖ ≤ Real.exp |Real.log u| := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hu, Complex.neg_re, Real.rpow_def_of_pos hu]
    apply Real.exp_le_exp.mpr
    have hm := abs_mul (Real.log u) (-s.re)
    have hh : |Real.log u| * |s.re| ≤ |Real.log u| := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hs (abs_nonneg (Real.log u))
    have hl := le_abs_self (Real.log u * -s.re)
    rw [hm, abs_neg] at hl
    exact hl.trans hh
  have he :=
    RectangleGeometry.integral_vertical_eq_of_strip_decay hf hc hd
      (mul_nonneg hC.le (Real.exp_pos _).le)
      (fun s hs ↦ by
        dsimp only [f]
        rw [norm_mul]
        calc
          _ ≤ (C / (1 + ‖s‖ ^ 2)) * Real.exp |Real.log u| :=
            mul_le_mul (hb s hs) (hpow s hs) (norm_nonneg _) (by positivity)
          _ = (C * Real.exp |Real.log u|) / (1 + ‖s‖ ^ 2) := by ring)
      (fun x _ ↦ by
        simpa only [f, mul_comm] using integrable_inverseMellin_triangular (c := x) ha.ne' hu)
  simpa only [f, mul_comm] using he

end PseudoPrime.AnalyticNumberTheory.General
