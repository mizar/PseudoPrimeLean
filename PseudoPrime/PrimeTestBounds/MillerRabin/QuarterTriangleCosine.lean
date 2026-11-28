/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.TriangularDigammaCorrection

/-! # Exact Cauchy moments of the wide triangle -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Height squared times the triangular kernel norm equals twice the cosine
defect, including at height zero. This gives the exact vertical moment integrand. -/
theorem triangle_height_cosine {a : ℝ} (ha : a ≠ 0) (t : ℝ) :
    t ^ 2 * ‖Analysis.triangularMellinFunction a (Complex.I * t)‖ =
      2 * (1 - Real.cos (2 * a * t)) := by
  rw [Analysis.norm_triangularMellinFunction_imaginary ha]
  have hs : (a * t) * Real.sinc (a * t) = Real.sin (a * t) := by
    by_cases ht : a * t = 0
    · simp only [ht, zero_mul, Real.sin_zero]
    · rw [Real.sinc_of_ne_zero ht, mul_div_cancel₀ _ ht]
  rw [show t ^ 2 * (2 * a * Real.sinc (a * t)) ^ 2 = 4 * ((a * t) * Real.sinc (a * t)) ^ 2 by ring,
    hs, mul_assoc, Real.cos_two_mul]
  nlinarith only [Real.sin_sq_add_cos_sq (a * t)]

/-- The exact vertical moment is the difference between the zero-frequency
and frequency 2a cosine integrals of the Cauchy density. -/
theorem triangle_moment_cosine {a c : ℝ} (ha : a ≠ 0) (hc : 0 < c) :
    (∫ t : ℝ, t ^ 2 * ‖Analysis.triangularMellinFunction a (Complex.I * t)‖ / (c ^ 2 + t ^ 2)) =
      2 * (Real.pi / c - ∫ t : ℝ, Real.cos (2 * a * t) / (c ^ 2 + t ^ 2)) := by
  let d (t : ℝ) := (c ^ 2 + t ^ 2)⁻¹
  have hd : MeasureTheory.Integrable d := Analysis.integrable_cauchy_of_pos hc
  have hcos : MeasureTheory.Integrable (fun t : ℝ => Real.cos (2 * a * t) / (c ^ 2 + t ^ 2)) := by
    have hcont : Continuous (fun t : ℝ => Real.cos (2 * a * t) / (c ^ 2 + t ^ 2)) := by
      apply
        Continuous.div (f := fun t : ℝ => Real.cos (2 * a * t)) (g := fun t : ℝ => c ^ 2 + t ^ 2)
          (by fun_prop) (by fun_prop)
      exact fun t => (add_pos_of_pos_of_nonneg (sq_pos_of_pos hc) (sq_nonneg t)).ne'
    apply hd.mono' hcont.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro t
    have ht := add_pos_of_pos_of_nonneg (sq_pos_of_pos hc) (sq_nonneg t)
    rw [Real.norm_eq_abs, abs_div, abs_of_pos ht]
    exact (div_le_div_of_nonneg_right (Real.abs_cos_le_one _) ht.le).trans_eq (one_div _)
  have he (t : ℝ) :
    t ^ 2 * ‖Analysis.triangularMellinFunction a (Complex.I * t)‖ / (c ^ 2 + t ^ 2) =
      2 * (d t - Real.cos (2 * a * t) / (c ^ 2 + t ^ 2)) := by
    rw [triangle_height_cosine ha]
    unfold d
    ring
  simp_rw [he]
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_sub hd hcos,
    show (∫ t : ℝ, d t) = Real.pi / c from Analysis.integral_univ_cauchy_of_pos hc]

/-- The integrated half-height digamma correction at a single pole is exactly
a scaled difference of Cauchy cosine integrals. -/
theorem triangle_digamma_pole {a r : ℝ} (ha : a ≠ 0) (hr : 0 < r) :
    (∫ t : ℝ,
        (1 / 2 : ℝ) * ((t / 2) ^ 2 / (r * (r ^ 2 + (t / 2) ^ 2))) *
          ‖Analysis.triangularMellinFunction a (Complex.I * t)‖) =
      (1 / r) * (Real.pi / (2 * r) - ∫ t : ℝ, Real.cos (2 * a * t) / ((2 * r) ^ 2 + t ^ 2)) := by
  simp_rw [Analysis.triangular_digamma_correction_term_eq_moment hr]
  rw [MeasureTheory.integral_const_mul, triangle_moment_cosine ha (by positivity)]
  ring

end PseudoPrime.PrimeTestBounds.MillerRabin
