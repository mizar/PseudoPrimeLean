/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPolePoleZero
public import PseudoPrime.LLS.PaperStatements.TriangularConductorFormula

/-! Inverse-scale reflection for the asymmetric refined six-pole kernel. -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The left-line kernel integral equals the original profile at inverse scale. -/
theorem refined_left_kernel_integral {x : ℝ} (hx : 0 < x) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          refinedSixPoleKernel.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
            (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) =
      (Analysis.rationalPoleProfile 3 (25 / 54) (21 / 16) x⁻¹ : ℂ) := by
  have h :=
    refined_six_pole_inversion (σ := (-9 / 16 : ℝ)) (u := x⁻¹) (by norm_num only) (inv_pos.mpr hx)
  unfold Analysis.inverseMellin at h
  simp only [Complex.ofReal_inv, Complex.cpow_neg, Complex.inv_cpow_ofReal_nonneg hx.le,
    inv_inv] at h
  exact h

/-- The reflected kernel has the original inverse-scale profile as its inverse Mellin transform. -/
theorem refined_reflected_inversion {u : ℝ} (hu : 0 < u) :
    Analysis.inverseMellin (fun z : ℂ ↦ refinedSixPoleKernel.function (-z)) (9 / 16) u =
      (Analysis.rationalPoleProfile 3 (25 / 54) (21 / 16) u⁻¹ : ℂ) := by
  have h := refined_left_kernel_integral (x := u) hu
  unfold Analysis.inverseMellin
  rw [← h]
  congr 1
  let F : ℝ → ℂ := fun t ↦
    refinedSixPoleKernel.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
      (u : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)
  have he (t : ℝ) :
    refinedSixPoleKernel.function (-(((9 / 16 : ℝ) : ℂ) + Complex.I * t)) *
        (u : ℂ) ^ (-(((9 / 16 : ℝ) : ℂ) + Complex.I * t)) =
      F (-t) := by
    dsimp only [F]
    have hz : -(((9 / 16 : ℝ) : ℂ) + Complex.I * t) = (((-9 / 16 : ℝ) : ℂ) + Complex.I * (-t)) := by
      simp only [Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_ofNat]
      ring
    rw [hz, Complex.ofReal_neg]
  change (∫ t : ℝ, _) = ∫ t : ℝ, F t
  rw [MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ he)]
  exact MeasureTheory.integral_neg_eq_self F MeasureTheory.volume

/-- Reflect the completed left contour and identify the exact inverse-scale conductor term. -/
theorem refined_left_reflection {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          -logDeriv χ.completedLFunction (((-9 / 16 : ℝ) : ℂ) + Complex.I * t + 1 / 2) *
            (refinedSixPoleKernel.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
              (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t))) =
      Complex.log q * (Analysis.rationalPoleProfile 3 (25 / 54) (21 / 16) x⁻¹ : ℂ) +
        ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            logDeriv χ⁻¹.completedLFunction (((17 / 16 : ℝ) : ℂ) - Complex.I * t) *
              (refinedSixPoleKernel.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
                (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t))) := by
  let K := refinedSixPoleKernel
  let w := fun t : ℝ ↦
    K.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
      (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)
  let F := fun t : ℝ ↦
    -logDeriv χ.completedLFunction (((-9 / 16 : ℝ) : ℂ) + Complex.I * t + 1 / 2) * w t
  let C := fun t : ℝ ↦ Complex.log q * w t
  let R := fun t : ℝ ↦ logDeriv χ⁻¹.completedLFunction (((17 / 16 : ℝ) : ℂ) - Complex.I * t) * w t
  have hd : K.delta = (1 / 8 : ℝ) := by
    norm_num only [K, refinedSixPoleKernel, LLS.PaperStatements.rationalPoleMellinKernel]
    apply min_eq_right
    norm_num only
  have hF :=
    LLS.PaperStatements.MellinKernel.integrable_completed_left_line K hp hne hinv (c := -9 / 16)
      (x := x)
      (by
        rw [hd]; norm_num only)
      (by norm_num only) (by norm_num only) hx
  have hC :=
    LLS.PaperStatements.MellinKernel.integrable_logWeighted_power_line K (c := -9 / 16) (x := x)
      (F := fun _ : ℝ ↦ Complex.log q) (A := ‖Complex.log q‖)
      (by
        rw [hd]; norm_num only)
      (by
        rw [hd]; norm_num only)
      (by norm_num only) hx MeasureTheory.aestronglyMeasurable_const
      (fun t ↦ by
        have hlog : 0 ≤ Real.log (4 + |t|) := Real.log_nonneg (by linarith only [abs_nonneg t])
        nlinarith only [hlog, norm_nonneg (Complex.log (q : ℂ))])
  simp only [mul_assoc] at hC
  change MeasureTheory.Integrable F at hF
  change MeasureTheory.Integrable C at hC
  have he (t : ℝ) : F t = C t + R t := by
    dsimp only [F, C, R]
    rw [LLS.PaperStatements.triangular18_completed_left_reflection hp hne hinv t, add_mul]
  have hR : MeasureTheory.Integrable R :=
    (hF.sub hC).congr
      (MeasureTheory.ae_of_all _ (fun t ↦ by rw [Pi.sub_apply, he, add_sub_cancel_left]))
  have hi : (∫ t : ℝ, F t) = (∫ t : ℝ, C t) + ∫ t : ℝ, R t := by
    rw [MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ he),
      MeasureTheory.integral_add hC hR]
  change ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ, F t) = _
  rw [hi, mul_add]
  have hcint :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ, C t) =
      Complex.log q * (Analysis.rationalPoleProfile 3 (25 / 54) (21 / 16) x⁻¹ : ℂ) := by
    dsimp only [C, w, K]
    rw [MeasureTheory.integral_const_mul]
    rw [← mul_assoc, mul_comm (((1 / (2 * Real.pi) : ℝ) : ℂ)) (Complex.log q), mul_assoc,
      refined_left_kernel_integral hx]
  rw [hcint]

/-- Reflect the contour using the reflected kernel and inverse scale. -/
theorem refined_reflected_integral (f : ℂ → ℂ) {x : ℝ} (hx : 0 < x) :
    (∫ t : ℝ,
        f (((17 / 16 : ℝ) : ℂ) - Complex.I * t) *
          (refinedSixPoleKernel.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
            (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t))) =
      (∫ t : ℝ,
        f ((((9 / 16 : ℝ) : ℂ) + Complex.I * t) + 1 / 2) *
          (refinedSixPoleKernel.function (-(((9 / 16 : ℝ) : ℂ) + Complex.I * t)) *
            ((x⁻¹ : ℝ) : ℂ) ^ (((9 / 16 : ℝ) : ℂ) + Complex.I * t))) := by
  let F := fun t : ℝ ↦
    f ((((9 / 16 : ℝ) : ℂ) + Complex.I * t) + 1 / 2) *
      (refinedSixPoleKernel.function (-(((9 / 16 : ℝ) : ℂ) + Complex.I * t)) *
        ((x⁻¹ : ℝ) : ℂ) ^ (((9 / 16 : ℝ) : ℂ) + Complex.I * t))
  have he (t : ℝ) :
    f (((17 / 16 : ℝ) : ℂ) - Complex.I * t) *
        (refinedSixPoleKernel.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
          (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) =
      F (-t) := by
    have hz : (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) = -(((9 / 16 : ℝ) : ℂ) + Complex.I * (-t)) := by
      simp only [Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_ofNat]
      ring
    have hw :
      (((17 / 16 : ℝ) : ℂ) - Complex.I * t) = (((9 / 16 : ℝ) : ℂ) + Complex.I * (-t)) + 1 / 2 := by
      simp only [Complex.ofReal_div, Complex.ofReal_ofNat]
      ring
    dsimp only [F]
    rw [hz, hw, Complex.cpow_neg, Complex.ofReal_inv, Complex.inv_cpow_ofReal_nonneg hx.le]
    simp only [Complex.ofReal_neg]
  change (∫ t : ℝ, _) = ∫ t : ℝ, F t
  rw [MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ he)]
  exact MeasureTheory.integral_neg_eq_self F MeasureTheory.volume

/-- Reflect the completed left integral to the dual kernel on the inverse scale. -/
theorem refined_left_reflection_dual {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          -logDeriv χ.completedLFunction (((-9 / 16 : ℝ) : ℂ) + Complex.I * t + 1 / 2) *
            (refinedSixPoleKernel.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
              (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t))) =
      Complex.log q * (Analysis.rationalPoleProfile 3 (25 / 54) (21 / 16) x⁻¹ : ℂ) +
        ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            logDeriv χ⁻¹.completedLFunction ((((9 / 16 : ℝ) : ℂ) + Complex.I * t) + 1 / 2) *
              (refinedSixPoleKernel.function (-(((9 / 16 : ℝ) : ℂ) + Complex.I * t)) *
                ((x⁻¹ : ℝ) : ℂ) ^ (((9 / 16 : ℝ) : ℂ) + Complex.I * t))) := by
  rw [refined_left_reflection hp hne hinv hx]
  rw [refined_reflected_integral (logDeriv χ⁻¹.completedLFunction) hx]

end PseudoPrime.PrimeTestBounds.MillerRabin
