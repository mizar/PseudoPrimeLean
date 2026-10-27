/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.TriangularMellin
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! # Integrable triangular moments for vertical digamma corrections -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For nonzero triangular parameter a and real height t, the height squared
kernel norm is at most four. Reduce to the sinc formula and sin squared at most one.
This provides a Cauchy majorant for the digamma correction terms. -/
theorem triangularMellinFunction_height_sq_norm_le_four {a : ℝ} (ha : a ≠ 0) (t : ℝ) :
    t ^ 2 * ‖triangularMellinFunction a (Complex.I * t)‖ ≤ 4 := by
  rw [norm_triangularMellinFunction_imaginary ha]
  have hs : (a * t) * Real.sinc (a * t) = Real.sin (a * t) := by
    by_cases ht : a * t = 0
    · simp only [ht, zero_mul, Real.sin_zero]
    · rw [Real.sinc_of_ne_zero ht, mul_div_cancel₀ _ ht]
  have he : t ^ 2 * (2 * a * Real.sinc (a * t)) ^ 2 = 4 * ((a * t) * Real.sinc (a * t)) ^ 2 := by
    ring
  rw [he, hs]
  exact mul_le_of_le_one_right (by norm_num only : (0 : ℝ) ≤ 4) (Real.sin_sq_le_one _)

end PseudoPrime.Analysis

namespace PseudoPrime.Analysis

/-- For nonzero c, factor the Cauchy denominator into a scale and the unit density.
Use the inverse cancellation identity with explicit nonzero denominator.
This connects the scaled density to the existing unit Cauchy integral. -/
theorem cauchy_scale_identity {c : ℝ} (hc : c ≠ 0) (t : ℝ) :
    (c ^ 2 + t ^ 2)⁻¹ = (c ^ 2)⁻¹ * (1 + (c⁻¹ * t) ^ 2)⁻¹ := by
  have he : (1 + (c⁻¹ * t) ^ 2) * c ^ 2 = c ^ 2 + t ^ 2 := by
    calc
      _ = c ^ 2 + (c⁻¹ * c) ^ 2 * t ^ 2 := by ring
      _ = _ := by
        rw [inv_mul_cancel₀ hc]; ring
  rw [← he, mul_inv_rev]

/-- For positive c, the Cauchy density integrates to pi/c. Scale the unit density
and use the known full-line integral. This evaluates the majorant for triangular moments. -/
theorem integral_univ_cauchy_of_pos {c : ℝ} (hc : 0 < c) :
    (∫ t : ℝ, (c ^ 2 + t ^ 2)⁻¹) = Real.pi / c := by
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (cauchy_scale_identity hc.ne')),
    MeasureTheory.integral_const_mul, integral_univ_inv_one_add_mul_sq, abs_of_pos (inv_pos.mpr hc),
    div_inv_eq_mul]
  calc
    _ = Real.pi * (c⁻¹ * c) * c⁻¹ := by
      rw [← inv_pow]; ring
    _ = _ := by
      rw [inv_mul_cancel₀ hc.ne']; simp only [mul_one, div_eq_mul_inv]

/-- For positive c, the Cauchy density is integrable. Transfer integrability from
the scaled unit density using the pointwise scale identity.
This justifies the integral comparison for each digamma correction term. -/
theorem integrable_cauchy_of_pos {c : ℝ} (hc : 0 < c) :
    MeasureTheory.Integrable (fun t : ℝ ↦ (c ^ 2 + t ^ 2)⁻¹) := by
  exact
    ((integrable_inv_one_add_mul_sq (inv_ne_zero hc.ne')).const_mul ((c ^ 2)⁻¹)).congr
      (Filter.Eventually.of_forall (fun t ↦ (cauchy_scale_identity hc.ne' t).symm))

end PseudoPrime.Analysis

namespace PseudoPrime.Analysis

/-- For nonzero a and positive c, the triangular height-squared Cauchy moment is
integrable and at most 4*pi/c. Its continuous integrand is dominated by the
integrable Cauchy density using the height bound.
This supplies the per-term integral budget for a signed Gamma correction. -/
theorem triangular_digamma_moment_integrable_and_bound {a c : ℝ} (ha : a ≠ 0) (hc : 0 < c) :
    MeasureTheory.Integrable
        (fun t : ℝ ↦ t ^ 2 * ‖triangularMellinFunction a (Complex.I * t)‖ / (c ^ 2 + t ^ 2)) ∧
      (∫ t : ℝ, t ^ 2 * ‖triangularMellinFunction a (Complex.I * t)‖ / (c ^ 2 + t ^ 2)) ≤
        4 * Real.pi / c := by
  let F := fun t : ℝ ↦ t ^ 2 * ‖triangularMellinFunction a (Complex.I * t)‖ / (c ^ 2 + t ^ 2)
  let G := fun t : ℝ ↦ 4 * (c ^ 2 + t ^ 2)⁻¹
  have hd (t : ℝ) : 0 < c ^ 2 + t ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos hc) (sq_nonneg t)
  have hb (t : ℝ) : F t ≤ G t := by
    have h :=
      div_le_div_of_nonneg_right (triangularMellinFunction_height_sq_norm_le_four ha t) (hd t).le
    simpa only [F, G, div_eq_mul_inv] using h
  have hK : Continuous (fun t : ℝ ↦ ‖triangularMellinFunction a (Complex.I * t)‖) :=
    ((differentiable_triangularMellinFunction a).continuous.comp
        (continuous_const.mul Complex.continuous_ofReal)).norm
  have hF : Continuous F :=
    ((continuous_id.pow 2).mul hK).div (continuous_const.add (continuous_id.pow 2))
      (fun t ↦ (hd t).ne')
  have hG : MeasureTheory.Integrable G := (integrable_cauchy_of_pos hc).const_mul 4
  have hi : MeasureTheory.Integrable F :=
    hG.mono' hF.aestronglyMeasurable
      (Filter.Eventually.of_forall
        (fun t ↦ by
          rw [Real.norm_eq_abs,
            abs_of_nonneg (div_nonneg (mul_nonneg (sq_nonneg t) (norm_nonneg _)) (hd t).le)]
          exact hb t))
  have hm := MeasureTheory.integral_mono hi hG hb
  rw [MeasureTheory.integral_const_mul, integral_univ_cauchy_of_pos hc] at hm
  exact ⟨hi, by simpa only [F, mul_div_assoc] using hm⟩

end PseudoPrime.Analysis

namespace PseudoPrime.Analysis

/-- For nonzero a and positive c, the Mellin-normalized triangular Cauchy moment
is at most 2/c. Divide the raw integral bound by the positive 2*pi.
This is the normalized input for summing vertical digamma corrections. -/
theorem triangular_digamma_normalized_moment_le {a c : ℝ} (ha : a ≠ 0) (hc : 0 < c) :
    (∫ t : ℝ, t ^ 2 * ‖triangularMellinFunction a (Complex.I * t)‖ / (c ^ 2 + t ^ 2)) /
        (2 * Real.pi) ≤
      2 / c := by
  have hm := (triangular_digamma_moment_integrable_and_bound ha hc).2
  have h := (le_div_iff₀ hc).mp hm
  apply (div_le_div_iff₀ (mul_pos (by norm_num only) Real.pi_pos) hc).mpr
  nlinarith only [h]

end PseudoPrime.Analysis
