/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannXi.UpperRectangle
public import PseudoPrime.AnalyticNumberTheory.RiemannXi.Conjugation

/-! # Integrability on the xi zero-count rectangle -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannXi

private theorem logDeriv_integrable_line (f : ℝ → ℂ) (hf : Continuous f)
    (h : ∀ x, riemannXi (f x) ≠ 0) (a b : ℝ) :
    IntervalIntegrable (fun x : ℝ ↦ logDeriv riemannXi (f x)) MeasureTheory.volume a b := by
  apply Continuous.intervalIntegrable
  apply continuous_iff_continuousAt.mpr
  intro x
  have hx :=
    (((differentiable_riemannXi.analyticAt (f x)).deriv).div
        (differentiable_riemannXi.analyticAt (f x)) (h x)).continuousAt
  change ContinuousAt (logDeriv riemannXi) (f x) at hx
  exact hx.comp hf.continuousAt

/-- Under RH at a good height, the xi logarithmic derivative is interval
integrable on all four edges of the upper zero-count rectangle. The bottom
and top are zero-free by RH and the good-height hypothesis, while the two
vertical lines lie outside the critical strip. -/
theorem upper_rectangle_logDeriv_integrable (hRH : RiemannHypothesis) {t : ℝ}
    (hgood : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 ≤ ρ.re → ρ.im ≠ t) :
    RectangleGeometry.RectangleBoundaryIntegrable (logDeriv riemannXi) ((-(1 / 2 : ℝ) : ℝ) : ℂ)
      (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) := by
  have hb :=
    logDeriv_integrable_line (fun x : ℝ ↦ (x : ℂ)) Complex.continuous_ofReal
      (riemannXi_real_ne_zero hRH) (-(1 / 2)) (3 / 2)
  have ht :=
    logDeriv_integrable_line (fun x : ℝ ↦ (x : ℂ) + (t : ℂ) * Complex.I)
      (Complex.continuous_ofReal.add continuous_const) (riemannXi_good_height_ne_zero hgood)
      (-(1 / 2)) (3 / 2)
  have hr :=
    logDeriv_integrable_line (fun y : ℝ ↦ ((3 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)
      (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))
      (fun y ↦ by
        apply riemannXi_ne_zero_of_one_lt_re
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_im, mul_zero]
        norm_num only)
      0 t
  have hl :=
    logDeriv_integrable_line (fun y : ℝ ↦ ((-(1 / 2 : ℝ) : ℝ) : ℂ) + (y : ℂ) * Complex.I)
      (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))
      (fun y ↦ by
        apply riemannXi_ne_zero_of_re_neg
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_im, mul_zero]
        norm_num only)
      0 t
  constructor
  · simpa only [Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, mul_zero, sub_zero, add_zero, Complex.ofReal_zero, zero_mul] using hb
  · simpa only [Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero,
      mul_one, zero_add] using ht
  · simpa only [Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero,
      mul_one, zero_add] using hr
  · simpa only [Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero,
      mul_one, zero_add] using hl

private theorem interval_im {f : ℝ → ℂ} {a b : ℝ}
    (hf : IntervalIntegrable f MeasureTheory.volume a b) :
    (∫ x in a..b, f x).im = ∫ x in a..b, (f x).im := by
  have h := Complex.imCLM.intervalIntegral_comp_comm hf
  simpa only [Complex.imCLM_apply] using h.symm

private theorem interval_re {f : ℝ → ℂ} {a b : ℝ}
    (hf : IntervalIntegrable f MeasureTheory.volume a b) :
    (∫ x in a..b, f x).re = ∫ x in a..b, (f x).re := by
  have h := Complex.reCLM.intervalIntegral_comp_comm hf
  simpa only [Complex.reCLM_apply] using h.symm

private theorem interval_im_integrable {f : ℝ → ℂ} {a b : ℝ}
    (hf : IntervalIntegrable f MeasureTheory.volume a b) :
    IntervalIntegrable (fun x ↦ (f x).im) MeasureTheory.volume a b := by
  apply intervalIntegrable_iff.mpr
  change MeasureTheory.Integrable (fun x ↦ (f x).im) (MeasureTheory.volume.restrict (Set.uIoc a b))
  simpa only [Function.comp_def, Complex.imCLM_apply] using Complex.imCLM.integrable_comp hf.def'

/-- Under RH at a good height, the imaginary part of the upper rectangle
boundary integral is twice the right-edge real integral minus twice the
right-half top-edge imaginary integral. Edge integrability permits taking
real and imaginary parts and splitting the upper integral at `1/2`. -/
theorem upper_rectangle_logDeriv_im (hRH : RiemannHypothesis) {t : ℝ}
    (hgood : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 ≤ ρ.re → ρ.im ≠ t) :
    (RectangleGeometry.rectangleBoundaryIntegral (logDeriv riemannXi) ((-(1 / 2 : ℝ) : ℝ) : ℂ)
          (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).im =
      2 *
        ((∫ y in (0 : ℝ)..t, (logDeriv riemannXi (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)).re) -
          ∫ x in (1 / 2 : ℝ)..(3 / 2),
            (logDeriv riemannXi ((x : ℂ) + (t : ℂ) * Complex.I)).im) := by
  have hedge := upper_rectangle_logDeriv_integrable hRH hgood
  have hb := hedge.bottom
  have ht := hedge.top
  have hr := hedge.right
  have hl := hedge.left
  simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero, mul_one, zero_add,
    Complex.ofReal_zero, zero_mul] at hb ht hr hl
  have hb0 : (∫ x in (-(1 / 2) : ℝ)..(3 / 2), (logDeriv riemannXi (x : ℂ)).im) = 0 := by
    simp only [logDeriv_riemannXi_real_im, intervalIntegral.integral_zero]
  have htop := interval_im_integrable ht
  have hs1 : Set.uIcc (-(1 / 2) : ℝ) (1 / 2) ⊆ Set.uIcc (-(1 / 2) : ℝ) (3 / 2) := by
    apply Set.uIcc_subset_uIcc
    · simp only [Set.mem_uIcc]
      left
      constructor <;> norm_num only
    · simp only [Set.mem_uIcc]
      left
      constructor <;> norm_num only
  have hs2 : Set.uIcc (1 / 2 : ℝ) (3 / 2) ⊆ Set.uIcc (-(1 / 2) : ℝ) (3 / 2) := by
    apply Set.uIcc_subset_uIcc
    · simp only [Set.mem_uIcc]
      left
      constructor <;> norm_num only
    · simp only [Set.mem_uIcc]
      left
      constructor <;> norm_num only
  have hs :=
    intervalIntegral.integral_add_adjacent_intervals (htop.mono_set hs1) (htop.mono_set hs2)
  have href := logDeriv_upper_horizontal_reflect t
  have hv := logDeriv_upper_vertical_reflect t
  unfold RectangleGeometry.rectangleBoundaryIntegral
  simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero, mul_one, zero_add,
    Complex.ofReal_zero, zero_mul, smul_eq_mul, Complex.sub_im, Complex.add_im]
  rw [interval_im hb, interval_im ht, interval_re hr, interval_re hl, hb0, hv, ← hs, href]
  ring

/-- Under RH at a positive good height, `π` times the positive zero count
equals the right-edge real integral minus the right-half top-edge imaginary
integral. Compare the finite residue formula with the reflected boundary
integral, retaining multiplicities and the closed height convention. -/
theorem positiveZeroCount_edge_integrals (hRH : RiemannHypothesis) {t : ℝ} (ht : 0 < t)
    (hgood : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 ≤ ρ.re → ρ.im ≠ t) :
    Real.pi * RiemannZeta.positiveZeroCount t =
      (∫ y in (0 : ℝ)..t, (logDeriv riemannXi (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)).re) -
        ∫ x in (1 / 2 : ℝ)..(3 / 2), (logDeriv riemannXi ((x : ℂ) + (t : ℂ) * Complex.I)).im := by
  have h := congrArg Complex.im (upper_rectangle_logDeriv_count hRH ht hgood)
  rw [upper_rectangle_logDeriv_im hRH hgood] at h
  norm_num only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, Complex.re_ofNat] at h
  linarith only [h]

end PseudoPrime.AnalyticNumberTheory.RiemannXi
