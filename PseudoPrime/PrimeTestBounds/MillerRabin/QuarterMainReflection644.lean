/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterThreeFrequency644
import all PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleDualReflection

/-! Inverse-scale reflection for the asymmetric refined six-pole kernel. -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- On every positive input and every line to the right of the sixth pole,
the inverse Mellin transform is the explicit nonnegative rational-pole
profile. This specializes the existing inversion theorem to the refined
parameters without changing its normalization. -/
theorem quarter_main_inversion_644 {σ u : ℝ} (hσ : 0 < σ + 107 / 100) (hu : 0 < u) :
    Analysis.inverseMellin (quarterKernel644.function) σ u =
      (Analysis.rationalPoleProfile 3 (50 / 107) (2687 / 2000) u : ℂ) := by
  change Analysis.inverseMellin (Analysis.rationalPoleFunction 3 (50 / 107) (2687 / 2000)) σ u = _
  apply Analysis.inverseMellin_rationalPole (m := 3) (by norm_num only) (by norm_num only) _ hu
  norm_num only at hσ ⊢
  exact hσ

/-- The left-line kernel integral equals the original profile at inverse scale. -/
theorem quarter_left_kernel_644 {x : ℝ} (hx : 0 < x) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          quarterKernel644.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
            (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) =
      (Analysis.rationalPoleProfile 3 (50 / 107) (2687 / 2000) x⁻¹ : ℂ) := by
  have h :=
    quarter_main_inversion_644 (σ := (-9 / 16 : ℝ)) (u := x⁻¹) (by norm_num only) (inv_pos.mpr hx)
  unfold Analysis.inverseMellin at h
  simp only [Complex.ofReal_inv, Complex.cpow_neg, Complex.inv_cpow_ofReal_nonneg hx.le,
    inv_inv] at h
  exact h

/-- Reflect the completed left contour and identify the exact inverse-scale
conductor term. -/
theorem quarter_main_reflection_644 {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          -logDeriv χ.completedLFunction (((-9 / 16 : ℝ) : ℂ) + Complex.I * t + 1 / 2) *
            (quarterKernel644.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
              (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t))) =
      Complex.log q * (Analysis.rationalPoleProfile 3 (50 / 107) (2687 / 2000) x⁻¹ : ℂ) +
        ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            logDeriv χ⁻¹.completedLFunction (((17 / 16 : ℝ) : ℂ) - Complex.I * t) *
              (quarterKernel644.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
                (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t))) := by
  let K := quarterKernel644
  let w := fun t : ℝ ↦
    K.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
      (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)
  let F := fun t : ℝ ↦
    -logDeriv χ.completedLFunction (((-9 / 16 : ℝ) : ℂ) + Complex.I * t + 1 / 2) * w t
  let C := fun t : ℝ ↦ Complex.log q * w t
  let R := fun t : ℝ ↦ logDeriv χ⁻¹.completedLFunction (((17 / 16 : ℝ) : ℂ) - Complex.I * t) * w t
  have hd : K.delta = (1 / 8 : ℝ) := by
    norm_num only [K, quarterKernel644, LLS.PaperStatements.rationalPoleMellinKernel]
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
      Complex.log q * (Analysis.rationalPoleProfile 3 (50 / 107) (2687 / 2000) x⁻¹ : ℂ) := by
    dsimp only [C, w, K]
    rw [MeasureTheory.integral_const_mul]
    rw [← mul_assoc, mul_comm (((1 / (2 * Real.pi) : ℝ) : ℂ)) (Complex.log q), mul_assoc,
      quarter_left_kernel_644 hx]
  rw [hcint]

/-- The main contour remainder splits into the inverse-scale conductor,
reflected completed logarithmic derivative and forward gamma integral. -/
theorem quarter_main_contour_reflect_644 {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hp : χ.IsPrimitive) (hn : χ ≠ 1) {x : ℝ} (hx : 0 < x) :
    let W := fun z : ℂ ↦ quarterKernel644.function z * (x : ℂ) ^ z
    let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    let r := fun t : ℝ ↦ ((9 / 16 : ℝ) : ℂ) + Complex.I * t
    let w := fun t : ℝ ↦ ((17 / 16 : ℝ) : ℂ) - Complex.I * t
    let d : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ)
    contourRemainder644 χ x =
      Complex.log q * (Analysis.rationalPoleProfile 3 (50 / 107) (2687 / 2000) x⁻¹ : ℂ) +
        d * (∫ t : ℝ, logDeriv χ⁻¹.completedLFunction (w t) * W (l t)) +
        d * (∫ t : ℝ, logDeriv χ.gammaFactor (r t + 1 / 2) * W (r t)) := by
  dsimp only
  rw [contour_no_residue_644, quarter_main_reflection_644 hp hn (inv_ne_one.mpr hn) hx]

end PseudoPrime.PrimeTestBounds.MillerRabin
