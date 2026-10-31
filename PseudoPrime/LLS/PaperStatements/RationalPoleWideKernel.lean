/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.RationalPoleContour
public import PseudoPrime.LLS.PaperStatements.RationalPoleFourStrip

/-! The fourth-order kernel with a symmetric allowance containing the left contour. -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- The original fourth-order function with region -4/5 < Re z < 4/5 and delta 27/100.
Holomorphy and decay use the symmetric-strip estimates. Prove Mellin integrability
and line independence on the enlarged allowed range directly from rational-pole inversion.
The transform, mass and all pointwise norm formulas are unchanged. This object admits
left contour -3/4 and right contour 5/8 in the existing contour-moving API. -/
noncomputable def fourWideKernel : MellinKernel :=
  { fourContourKernel with
    delta := 27 / 100
    delta_pos := by norm_num only
    region := fourWideRegion
    region_open :=
      (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)
    strip_subset := by
      intro z hz
      change -(4 / 5 : ℝ) < z.re ∧ z.re < 4 / 5
      change (-1 / 2 - 27 / 100 : ℝ) < z.re ∧ z.re ≤ 1 / 2 + 27 / 100 at hz
      constructor <;> linarith only [hz.1, hz.2]
    holomorphic := fun z hz ↦ (fourWide_differentiableAt hz.1).differentiableWithinAt
    regularized_holomorphic := by
      intro z hz
      exact
        (((differentiableAt_id (𝕜 := ℂ) (x := z)).add_const (1 / 2)).mul
            (fourWide_differentiableAt hz)).differentiableWithinAt
    regularized_eq := fun _ _ _ ↦ rfl
    decay := by
      intro η _
      refine ⟨(26 / 25 : ℝ) * Real.exp 2 * 100 / (21 / 125 : ℝ) ^ 2, ?_, ?_⟩
      · exact
          div_pos (mul_pos (mul_pos (by norm_num only) (Real.exp_pos 2)) (by norm_num only))
            (pow_pos (by norm_num only) 2)
      · exact fun z hz _ ↦ fourWide_norm_le hz
    mellin_integrable := by
      intro σ u hσ _ hu
      change
        MeasureTheory.Integrable
          (fun t : ℝ ↦
            Analysis.rationalPoleFunction 2 (13 / 25) (14 / 25) ((σ : ℂ) + Complex.I * t) *
              (u : ℂ) ^ (-((σ : ℂ) + Complex.I * t)))
      exact
        integrable_inverseMellin_of_line hu
          (integrable_rationalPole_line (m := 2) (a := 13 / 25) (σ := σ) (by norm_num only)
            (by norm_num only)
            (by
              norm_num only; linarith only [hσ])
            (14 / 25))
    mellin_eq := by
      intro σ u hσ _ hu
      change
        Analysis.inverseMellin (Analysis.rationalPoleFunction 2 (13 / 25) (14 / 25)) σ u =
          Analysis.inverseMellin (Analysis.rationalPoleFunction 2 (13 / 25) (14 / 25)) 0 u
      rw [Analysis.inverseMellin_rationalPole (m := 2) (a := 13 / 25) (by norm_num only)
          (by norm_num only)
          (by
            norm_num only; linarith only [hσ])
          hu (14 / 25),
        Analysis.inverseMellin_rationalPole (m := 2) (a := 13 / 25) (by norm_num only)
          (by norm_num only) (by norm_num only) hu (14 / 25)] }

/-- The wider symmetric allowance preserves the fourth-order kernel mass one quarter.
The function is unchanged, so the certified contour-kernel mass applies directly. -/
theorem fourWide_mass : fourWideKernel.mass = 1 / 4 := by exact fourContour_mass

/-- The wider kernel has the original contour-kernel transform at every real input.
Only admissibility data change. This transfers all existing cutoff calculations. -/
theorem fourWide_transform_eq (u : ℝ) :
    fourWideKernel.transform u = fourContourKernel.transform u :=
  rfl

/-- The wider symmetric kernel retains the exact unit cutoff principal integral.
Rewrite its transform and apply the existing fourth-order cutoff certificate. -/
theorem fourWide_cutoff :
    (∫ u : ℝ in (0 : ℝ)..1, (fourWideKernel.transform u).re / Real.sqrt u) =
      (484820459 / 528581976 : ℝ) * Real.exp (-(14 / 13)) := by
  simp only [fourWide_transform_eq]
  exact fourContour_cutoff

end PseudoPrime.LLS.PaperStatements
