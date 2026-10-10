/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.TriangularMellin
public import PseudoPrime.AnalyticNumberTheory.General.TriangularMellinInversion
public import PseudoPrime.AnalyticNumberTheory.General.TriangularMellinContour
public import PseudoPrime.LLS.TheoreticalKernelProfiles
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Triangular kernel mass from its Mellin transform

Imaginary-axis positivity identifies the mass with the transform at one.
A triangular transform therefore determines the mass without a separate
sinc-square integral hypothesis.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- On a positive vertical line, the inverse Mellin transform of the
triangular kernel is its real triangular profile for positive parameter
and argument. Convert integral conventions and apply the computed
three-logarithmic-weight inversion. This supplies the Section 6.2 identity. -/
theorem inverseMellin_triangular_pos {a c u : ℝ} (ha : 0 < a) (hc : 0 < c) (hu : 0 < u) :
    inverseMellin (Analysis.triangularMellinFunction a) c u =
      ((triangularKernelProfile a u : ℝ) : ℂ) := by
  unfold triangularKernelProfile
  rw [← AnalyticNumberTheory.General.mellinInv_triangular_of_pos ha hc hu]
  unfold inverseMellin mellinInv
  rw [Complex.real_smul]
  congr 1
  apply MeasureTheory.integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  dsimp only
  simp only [smul_eq_mul, mul_comm]

/-- An admissible kernel with the triangular function has the triangular
real transform at every positive argument. Move its inverse integral to
the line of real coordinate one quarter using the kernel's line independence,
then apply positive-line inversion. This removes the transform hypothesis
from the triangular specialization of Proposition 6.1. -/
theorem triangular_transform_of_function (K : MellinKernel) {a : ℝ} (ha : 0 < a)
    (hf : K.function = Analysis.triangularMellinFunction a) {u : ℝ} (hu : 0 < u) :
    (K.transform u).re = triangularKernelProfile a u := by
  have hc : (1 / 4 : ℝ) ≤ 1 / 2 + K.delta := by linarith only [K.delta_pos]
  rw [MellinKernel.transform, ← K.mellin_eq (1 / 4) u (by norm_num only) hc hu, hf,
    inverseMellin_triangular_pos ha (by norm_num only) hu, Complex.ofReal_re]

/-- For a triangular kernel with nonzero parameter, the mass equals the
real transform at one. Its imaginary-axis values are nonnegative real
squares, so the norm integral is exactly the inverse-Mellin integral
at one. This avoids a separate sinc-square integration assumption. -/
theorem triangular_mass_eq_transform_one (K : MellinKernel) {a : ℝ} (ha : a ≠ 0)
    (hf : K.function = Analysis.triangularMellinFunction a) : K.mass = (K.transform 1).re := by
  have hi :
    (MeasureTheory.integral MeasureTheory.volume (fun t : ℝ ↦ K.function (Complex.I * t))).re =
      MeasureTheory.integral MeasureTheory.volume (fun t : ℝ ↦ ‖K.function (Complex.I * t)‖) := by
    rw [hf]
    simp only [Analysis.norm_triangularMellinFunction_imaginary ha]
    simp only [Analysis.triangularMellinFunction_imaginary ha, integral_complex_ofReal,
      Complex.ofReal_re]
  rw [MellinKernel.transform, inverseMellin]
  simp only [Complex.ofReal_zero, zero_add, Complex.ofReal_one, Complex.one_cpow, mul_one,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, hi]
  unfold MellinKernel.mass
  ring

/-- The triangular function identity fixes the kernel mass as `2*a`
for positive parameter. Evaluate the transform at one, where the
logarithm vanishes, and use the imaginary-axis positivity identity.
This supplies the mass required by Proposition 6.1. -/
theorem triangular_mass_of_function (K : MellinKernel) {a : ℝ} (ha : 0 < a)
    (hf : K.function = Analysis.triangularMellinFunction a) : K.mass = 2 * a := by
  rw [triangular_mass_eq_transform_one K ha.ne' hf,
    triangular_transform_of_function K ha hf (by norm_num only : (0 : ℝ) < 1)]
  unfold triangularKernelProfile
  rw [Real.log_one, abs_zero, sub_zero, max_eq_right]
  exact mul_nonneg (by norm_num only) ha.le

/-- For a positive parameter and argument, the inverse Mellin transform is
the triangular profile on every line in the closed unit strip, including
the imaginary axis. Line independence reduces the computation to a positive
line where the three logarithmic weights have already been inverted. This
supplies the transform fields of the concrete triangular Mellin kernel. -/
theorem inverseMellin_triangular {a c u : ℝ} (ha : 0 < a) (hc : |c| ≤ 1) (hu : 0 < u) :
    inverseMellin (Analysis.triangularMellinFunction a) c u =
      (triangularKernelProfile a u : ℂ) := by
  have he :=
    AnalyticNumberTheory.General.integral_triangular_vertical_eq ha hu hc (c := c) (d := 1 / 4)
      (by norm_num only [abs_of_nonneg (by norm_num only : (0 : ℝ) ≤ 1 / 4)])
  have hi :
    inverseMellin (Analysis.triangularMellinFunction a) c u =
      inverseMellin (Analysis.triangularMellinFunction a) (1 / 4) u := by
    unfold inverseMellin
    rw [he]
  exact hi.trans (inverseMellin_triangular_pos ha (by norm_num only) hu)

end PseudoPrime.LLS.PaperStatements
