/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.RationalPoleKernelMass
public import PseudoPrime.LLS.RationalPoleFourStrip
public import PseudoPrime.LLS.RationalPoleCertificates
/-! Extended admissibility for the fourth-order kernel and the left contour at -3/4. -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements
/-- An open vertical strip extending from real part -4/5 to 3/4.
It contains the proposed left contour at -3/4 and excludes the fourth-order pole -25/26.
The upper edge and original admissibility strip remain covered. -/
def fourContourRegion : Set ℂ := {z | -(4 / 5 : ℝ) < z.re ∧ z.re < 3 / 4}

/-- In the extended strip the fourth-order denominator stays uniformly away from zero,
and its squared norm controls one plus the squared norm of the argument.
Use the real-part gap 21/125 and the explicit imaginary coefficient 26/25.
These two bounds supply holomorphy and uniform quadratic decay on the enlarged region. -/
theorem fourContour_denominator_bounds {z : ℂ} (hz : z ∈ fourContourRegion) :
    (21 / 125 : ℝ) ^ 2 ≤ ‖1 + (26 / 25 : ℂ) * z‖ ^ 2 ∧
    1 + ‖z‖ ^ 2 ≤ 100 * ‖1 + (26 / 25 : ℂ) * z‖ ^ 2 := by
  exact fourWide_denominator_bounds ⟨hz.1, hz.2.trans (by norm_num only)⟩

/-- The actual fourth-order kernel is complex differentiable throughout the enlarged strip.
Its denominator is nonzero by the quantitative gap, and its exponential numerator is entire.
This proves the additional holomorphy needed to move the left contour to -3/4. -/
theorem fourContour_differentiableAt {z : ℂ} (hz : z ∈ fourContourRegion) :
    DifferentiableAt ℂ rationalPoleFourKernel.function z := by
  exact fourWide_differentiableAt ⟨hz.1, hz.2.trans (by norm_num only)⟩

/-- Throughout the extended strip, the actual fourth-order kernel has a uniform quadratic
decay bound with an explicit positive constant. Bound exponential modulation by exp(2)
and use both denominator inequalities to reduce the fourth power to quadratic decay.
The estimate holds without excluding the point -1/2 because this kernel is regular there. -/
theorem fourContour_norm_le {z : ℂ} (hz : z ∈ fourContourRegion) :
    ‖rationalPoleFourKernel.function z‖ ≤
      ((26 / 25 : ℝ) * Real.exp 2 * 100 / (21 / 125 : ℝ) ^ 2) / (1 + ‖z‖ ^ 2) := by
  exact fourWide_norm_le ⟨hz.1, hz.2.trans (by norm_num only)⟩

/-- The same fourth-order Mellin kernel with its region enlarged to the contour strip.
Keep the function, regularization, delta, inverse transform and positivity data unchanged.
Prove holomorphy and decay on the larger region using the new denominator estimates.
This provides an admissible object whose region contains the proposed -3/4 contour. -/
noncomputable def fourContourKernel : MellinKernel :=
  { rationalPoleFourKernel with
    region := fourContourRegion
    region_open := (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
    strip_subset := by
      intro z hz
      have hs := rationalPoleFourKernel.strip_subset hz
      norm_num only [rationalPoleFourKernel, rationalPoleMellinKernel, reciprocalGapRegion,
        min_def, ite_true] at hs
      exact ⟨by linarith only [hs.1], hs.2⟩
    holomorphic := fun z hz ↦ (fourContour_differentiableAt hz.1).differentiableWithinAt
    regularized_holomorphic := by
      intro z hz
      exact (((differentiableAt_id (𝕜 := ℂ) (x := z)).add_const (1 / 2)).mul
        (fourContour_differentiableAt hz)).differentiableWithinAt
    regularized_eq := fun _ _ _ ↦ rfl
    decay := by
      intro η _
      refine ⟨(26 / 25 : ℝ) * Real.exp 2 * 100 / (21 / 125 : ℝ) ^ 2, ?_, ?_⟩
      · exact div_pos (mul_pos (mul_pos (by norm_num only) (Real.exp_pos 2))
          (by norm_num only)) (pow_pos (by norm_num only) 2)
      · exact fun z hz _ ↦ fourContour_norm_le hz }

/-- Every point of the left contour with real part -3/4 lies in the enlarged kernel region.
Compute its real part explicitly. This discharges region membership for contour consumers. -/
theorem fourContour_left_mem (t : ℝ) : (-3 / 4 : ℂ) + Complex.I * t ∈ fourContourKernel.region := by
  change -(4 / 5 : ℝ) < ((-3 / 4 : ℂ) + Complex.I * t).re ∧
    ((-3 / 4 : ℂ) + Complex.I * t).re < 3 / 4
  norm_num only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re, Complex.div_re,
    Complex.re_ofNat, Complex.im_ofNat, Complex.normSq_apply, mul_zero, mul_one,
    zero_mul, sub_zero, add_zero, and_self]

/-- Enlarging the region preserves the actual kernel mass because its function is unchanged.
This transfers the existing fourth-order mass certificate to the contour kernel. -/
theorem fourContour_mass_eq : fourContourKernel.mass = rationalPoleFourKernel.mass := rfl

/-- The enlarged kernel has exactly the original inverse transform at every real argument.
Both transforms use the same function, so all prior cutoff integrals remain applicable. -/
theorem fourContour_transform_eq (u : ℝ) :
    fourContourKernel.transform u = rationalPoleFourKernel.transform u := rfl

/-- The enlarged kernel is absolutely integrable on the entire left contour at -3/4.
This line lies right of its actual pole; apply the general rational-pole line theorem.
It supplies the unweighted line-integrability input for finite contour estimates. -/
theorem fourContour_left_integrable : MeasureTheory.Integrable (fun t : ℝ ↦
    fourContourKernel.function ((-3 / 4 : ℂ) + Complex.I * t)) := by
  change MeasureTheory.Integrable (fun t : ℝ ↦
    Analysis.rationalPoleFunction 2 (13 / 25) (14 / 25) ((-3 / 4 : ℂ) + Complex.I * t))
  simpa only [Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_ofNat] using
    (integrable_rationalPole_line (m := 2) (a := (13 / 25 : ℝ)) (σ := (-3 / 4 : ℝ))
    (by norm_num only : (1 : ℕ) ≤ 2) (by norm_num only : (0 : ℝ) < 13 / 25)
    (by norm_num only : (0 : ℝ) < -3 / 4 + (2 * (13 / 25 : ℝ))⁻¹) (14 / 25))

/-- The extended contour kernel retains the certified mass one quarter.
Transfer the original mass through equality of the unchanged functions.
This keeps the conductor coefficient of the fourth-order candidate unchanged. -/
theorem fourContour_mass : fourContourKernel.mass = 1 / 4 := by
  rw [fourContour_mass_eq]
  exact rationalPole_four_mass (by norm_num only) (by norm_num only)

/-- The extended contour kernel retains the exact unit-cutoff principal integral.
Rewrite its transform to the original fourth-order transform and use the existing
rational moment calculation. Thus widening the region loses no principal mass. -/
theorem fourContour_cutoff :
    (∫ u : ℝ in (0:ℝ)..1, (fourContourKernel.transform u).re / Real.sqrt u) =
      (484820459 / 528581976 : ℝ) * Real.exp (-(14 / 13)) := by
  simp only [fourContour_transform_eq]
  exact rationalPole_four_cutoff

/-- The enlarged admissible kernel retains the strict 777/1000 coefficient margin
after the two-node Poisson majorant loss. Its function and transform are unchanged,
so the prior certificate applies. This is still a prerequisite for a finite entrance,
not a bound for all remaining principal, gamma, contour and local error terms. -/
theorem fourContour_majorant_margin :
    ((poleFourUpperWeight - poleFourLowerWeight) / 2) ^ 2 <
      (777 / 1000 : ℝ) * (2 * (∫ u : ℝ in (0:ℝ)..1,
        (fourContourKernel.transform u).re / Real.sqrt u) -
          (fourContourKernel.function (1 / 2)).re) ^ 2 := by
  change ((poleFourUpperWeight - poleFourLowerWeight) / 2) ^ 2 <
    (777 / 1000 : ℝ) * (2 * (∫ u : ℝ in (0:ℝ)..1,
      (rationalPoleFourKernel.transform u).re / Real.sqrt u) -
        (rationalPoleFourKernel.function (1 / 2)).re) ^ 2
  exact rationalPole_four_majorant_margin

end PseudoPrime.LLS.PaperStatements
