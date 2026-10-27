/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaSubtractedMellin

/-!
# Gamma inversion on the negative strip

The inverse transform includes the subtracted origin residue. This is the exact
constant-conductor contribution needed on a left Mellin line.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- A vertical line of nonzero real part avoids zero. Comparing real parts supplies
the denominator nonvanishing for shifting Gamma by one. -/
theorem verticalPoint_ne_zero {c : ℝ} (hc : c ≠ 0) (t : ℝ) : ((c : ℂ) + t * Complex.I) ≠ 0 := by
  intro he
  have hr := congrArg Complex.re he
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, zero_mul, mul_zero, sub_zero, add_zero, Complex.zero_re] at hr
  exact hc hr

/-- For c < 0, Gamma on the vertical line c is its shifted value divided by c+it.
The recurrence keeps the negative-line inversion attached to its origin subtraction. -/
theorem Gamma_negative_vertical_eq_div {c : ℝ} (hc : c < 0) (t : ℝ) :
    Complex.Gamma ((c : ℂ) + t * Complex.I) =
      Complex.Gamma (((c + 1 : ℝ) : ℂ) + t * Complex.I) / ((c : ℂ) + t * Complex.I) := by
  apply (eq_div_iff (verticalPoint_ne_zero hc.ne t)).mpr
  have hs : (((c + 1 : ℝ) : ℂ) + t * Complex.I) = ((c : ℂ) + t * Complex.I) + 1 := by
    rw [Complex.ofReal_add, Complex.ofReal_one]
    ring
  rw [hs, Complex.Gamma_add_one _ (verticalPoint_ne_zero hc.ne t)]
  ring

/-- The inverse denominator on a negative vertical line has norm at most (-c) inverse.
Use the absolute real part as a uniform norm lower bound. -/
theorem norm_negative_vertical_inv_le {c : ℝ} (hc : c < 0) (t : ℝ) :
    ‖((c : ℂ) + t * Complex.I)⁻¹‖ ≤ (-c)⁻¹ := by
  have hl := Complex.abs_re_le_norm ((c : ℂ) + t * Complex.I)
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, zero_mul, mul_zero, sub_zero, add_zero, abs_of_neg hc] at hl
  rw [norm_inv]
  exact (inv_le_inv₀ (lt_of_lt_of_le (neg_pos.mpr hc) hl) (neg_pos.mpr hc)).mpr hl

/-- Gamma on -1 < c < 0 is continuous as a shifted positive-line Gamma quotient.
This supplies measurability independently of a contour-shift assertion. -/
theorem continuous_Gamma_negative_vertical {c : ℝ} (hlo : -1 < c) (hhi : c < 0) :
    Continuous (fun t : ℝ ↦ Complex.Gamma ((c : ℂ) + t * Complex.I)) := by
  have hp : 0 < c + 1 := by linarith only [hlo]
  have h :=
    (continuous_Gamma_vertical hp).div
      (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))
      (verticalPoint_ne_zero hhi.ne)
  exact
    h.congr
      (fun t ↦ by
        simpa only [Pi.div_apply, Pi.add_apply, Pi.mul_apply, mul_comm] using
          (Gamma_negative_vertical_eq_div hhi t).symm)

/-- Gamma is absolutely integrable on every negative vertical line -1 < c < 0.
Bound the reciprocal recurrence factor uniformly and use positive-line integrability. -/
theorem integrable_Gamma_negative_vertical {c : ℝ} (hlo : -1 < c) (hhi : c < 0) :
    MeasureTheory.Integrable (fun t : ℝ ↦ Complex.Gamma ((c : ℂ) + t * Complex.I)) := by
  have hp : 0 < c + 1 := by linarith only [hlo]
  have hf :=
    (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).inv₀
      (verticalPoint_ne_zero hhi.ne)
  have h :=
    (integrable_Gamma_vertical hp).bdd_mul hf.aestronglyMeasurable
      (Filter.Eventually.of_forall (norm_negative_vertical_inv_le hhi))
  apply h.congr
  exact
    Filter.Eventually.of_forall
      (fun t ↦ by
        simpa only [Pi.inv_apply, Pi.add_apply, Pi.mul_apply, div_eq_mul_inv, mul_comm] using
          (Gamma_negative_vertical_eq_div hhi t).symm)

/-- For -1 < c < 0 and u > 0, the inverse Gamma Mellin transform is exp(-u)-1.
Apply actual Mellin inversion to the subtracted density with both convergence inputs.
The minus one is the origin residue, not a discarded absolute-value error. -/
theorem mellinInv_Gamma_negative {c u : ℝ} (hlo : -1 < c) (hhi : c < 0) (hu : 0 < u) :
    mellinInv c Complex.Gamma u = (Real.exp (-u) - 1 : ℝ) := by
  have he :
    ∀ t : ℝ,
      mellin gammaSubtractedDensity ((c : ℂ) + t * Complex.I) =
        Complex.Gamma ((c : ℂ) + t * Complex.I) := by
    intro t
    apply mellin_gammaSubtractedDensity
    · simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, zero_mul, mul_zero, sub_zero, add_zero] using hlo
    · simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, zero_mul, mul_zero, sub_zero, add_zero] using hhi
  have hv : Complex.VerticalIntegrable (mellin gammaSubtractedDensity) c := by
    exact
      (integrable_Gamma_negative_vertical hlo hhi).congr
        (Filter.Eventually.of_forall (fun t ↦ (he t).symm))
  have hi :=
    mellinInv_mellin_eq c gammaSubtractedDensity hu
      (mellinConvergent_gammaSubtractedDensity (by simpa only [Complex.ofReal_re] using hlo)
        (by simpa only [Complex.ofReal_re] using hhi))
      hv (continuous_gammaSubtractedDensity.continuousAt)
  apply Eq.trans _ hi
  dsimp only [mellinInv]
  congr 1
  apply MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall (fun t ↦ by simp only [he])

end PseudoPrime.Analysis
