/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TriangularKernelIdentities

/-! # The admissible triangular Mellin kernel

The entire exponential quotient has uniform strip decay and a nonnegative
compactly supported triangular inverse transform. All admissibility fields
are proved, including integration-line independence across the imaginary axis.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- The Section 6.2 triangular Mellin kernel with positive parameter `a`
and strip width `1/8`. The function is entire; multiplication by `s+1/2`
gives a holomorphic regularization. Quadratic decay, absolute integrability,
and the triangular inverse transform establish all admissibility conditions.
This concrete kernel supplies the large-index specialization of Proposition 6.1. -/
noncomputable def triangularMellinKernel {a : ℝ} (ha : 0 < a) : MellinKernel where
  function := Analysis.triangularMellinFunction a
  delta := 1 / 8
  delta_pos := by norm_num only
  region := {s : ℂ | -3 / 4 < s.re ∧ s.re < 3 / 4}
  region_open :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  strip_subset := by
    intro s hs
    exact ⟨by linarith only [hs.1], by linarith only [hs.2]⟩
  holomorphic := (Analysis.differentiable_triangularMellinFunction a).differentiableOn
  regularized s := (s + 1 / 2) * Analysis.triangularMellinFunction a s
  regularized_holomorphic :=
    ((differentiable_id.add_const _).mul
        (Analysis.differentiable_triangularMellinFunction a)).differentiableOn
  regularized_eq := fun _ _ _ ↦ rfl
  decay := by
    intro η _
    obtain ⟨C, hC, hb⟩ := Analysis.triangularMellinFunction_strip_bound ha
    refine ⟨C, hC, ?_⟩
    intro s hs _
    exact hb s (abs_le.mpr ⟨by linarith only [hs.1], by linarith only [hs.2]⟩)
  mellin_integrable := fun _ _ _ _ hu ↦
    AnalyticNumberTheory.General.integrable_inverseMellin_triangular ha.ne' hu
  mellin_eq := by
    intro c u hc hd hu
    have hc' : |c| ≤ 1 := abs_le.mpr ⟨by linarith only [hc], by linarith only [hd]⟩
    rw [inverseMellin_triangular ha hc' hu,
      inverseMellin_triangular ha (by norm_num only [abs_zero]) hu]
  mellin_nonneg := by
    intro u hu
    rw [inverseMellin_triangular ha (by norm_num only [abs_zero]) hu, Complex.ofReal_re]
    exact triangularKernelProfile_nonneg a u
  mellin_nonzero := by
    refine ⟨1, by norm_num only, ?_⟩
    rw [inverseMellin_triangular ha (by norm_num only [abs_zero]) (by norm_num only),
      Complex.ofReal_re]
    exact (triangularKernelProfile_one ha).ne'
  mellin_real := by
    intro u hu
    rw [inverseMellin_triangular ha (by norm_num only [abs_zero]) hu, Complex.ofReal_im]

end PseudoPrime.LLS.PaperStatements
