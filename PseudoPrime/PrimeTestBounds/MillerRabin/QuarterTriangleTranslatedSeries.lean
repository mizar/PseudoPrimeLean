/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterTriangleFourier

/-! # Cosine-modulated digamma correction of the translated triangle -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The cosine-modulated Cauchy density is integrable for every frequency. -/
private theorem cosine_density_integrable {c : ℝ} (hc : 0 < c) (v : ℝ) :
    MeasureTheory.Integrable (fun t : ℝ => Real.cos (v * t) / (c ^ 2 + t ^ 2)) := by
  have hd (t : ℝ) := add_pos_of_pos_of_nonneg (sq_pos_of_pos hc) (sq_nonneg t)
  apply
    (Analysis.integrable_cauchy_of_pos hc).mono'
      ((Continuous.div (f := fun t : ℝ => Real.cos (v * t)) (g := fun t => c ^ 2 + t ^ 2)
          (by fun_prop) (by fun_prop) (fun t => (hd t).ne')).aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro t
  change ‖Real.cos (v * t) / (c ^ 2 + t ^ 2)‖ ≤ _
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (hd t)]
  exact (div_le_div_of_nonneg_right (Real.abs_cos_le_one _) (hd t).le).trans_eq (one_div _)

/-- Multiplying the triangle height moment by a cosine translates its Cauchy
transform to three frequencies, giving the signed second difference. -/
theorem triangle_translated_moment {a c : ℝ} (ha : a ≠ 0) (hc : 0 < c) (v : ℝ) :
    (∫ t : ℝ,
        t ^ 2 * ‖Analysis.triangularMellinFunction a (Complex.I * t)‖ / (c ^ 2 + t ^ 2) *
          Real.cos (v * t)) =
      Real.pi / c *
        (2 * Real.exp (-c * |v|) - Real.exp (-c * |v + 2 * a|) - Real.exp (-c * |v - 2 * a|)) := by
  let f (z t : ℝ) := Real.cos (z * t) / (c ^ 2 + t ^ 2)
  have he (t : ℝ) :
    t ^ 2 * ‖Analysis.triangularMellinFunction a (Complex.I * t)‖ / (c ^ 2 + t ^ 2) *
        Real.cos (v * t) =
      2 * f v t - f (v + 2 * a) t - f (v - 2 * a) t := by
    rw [triangle_height_cosine ha]
    unfold f
    rw [add_mul, sub_mul, Real.cos_add, Real.cos_sub]
    ring
  simp_rw [he]
  have hi (z : ℝ) : MeasureTheory.Integrable (f z) := cosine_density_integrable hc z
  have hi2 : MeasureTheory.Integrable (fun t => 2 * f v t - f (v + 2 * a) t) :=
    ((hi v).const_mul 2).sub (hi _)
  rw [MeasureTheory.integral_sub hi2 (hi (v - 2 * a)),
    MeasureTheory.integral_sub ((hi v).const_mul 2) (hi _), MeasureTheory.integral_const_mul]
  unfold f
  rw [triangle_cauchy_cosine hc, triangle_cauchy_cosine hc, triangle_cauchy_cosine hc]
  ring

/-- Once the translated triangle lies on the positive half-line, each pole
contributes a negative exponential times a square. -/
theorem triangle_translated_pole {a r v : ℝ} (ha : 0 < a) (hr : 0 < r) (hv : 2 * a ≤ v) :
    (∫ t : ℝ,
        (1 / 2 : ℝ) * ((t / 2) ^ 2 / (r * (r ^ 2 + (t / 2) ^ 2))) *
          ‖Analysis.triangularMellinFunction a (Complex.I * t)‖ *
          Real.cos (v * t)) =
      -(Real.pi / (4 * r ^ 2)) * Real.exp (-(2 * r) * (v - 2 * a)) *
        (1 - Real.exp (-(4 * a * r))) ^ 2 := by
  simp_rw [Analysis.triangular_digamma_correction_term_eq_moment hr, mul_assoc]
  rw [MeasureTheory.integral_const_mul, triangle_translated_moment ha.ne' (by positivity),
    abs_of_nonneg (show 0 ≤ v by linarith only [ha, hv]),
    abs_of_nonneg (show 0 ≤ v + 2 * a by linarith only [ha, hv]), abs_of_nonneg (sub_nonneg.mpr hv)]
  have he :
    Real.exp (-(2 * r) * v) = Real.exp (-(2 * r) * (v - 2 * a)) * Real.exp (-(4 * a * r)) := by
    rw [← Real.exp_add]; congr 1; ring
  have he' :
    Real.exp (-(2 * r) * (v + 2 * a)) =
      Real.exp (-(2 * r) * (v - 2 * a)) * Real.exp (-(4 * a * r)) ^ 2 := by
    rw [sq, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  rw [he, he']
  field_simp
  ring

/-- Modulating the positive pole expansion by a cosine preserves absolute
integrability. The translated digamma integral is the sum of the negative pole terms. -/
theorem triangle_translated_series {a b v : ℝ} (ha : 0 < a) (hb : 0 < b) (hv : 2 * a ≤ v) :
    (∫ t : ℝ,
        (1 / 2 : ℝ) *
          ((Complex.digamma ((b : ℂ) + Complex.I * (t / 2))).re - (Complex.digamma (b : ℂ)).re) *
          ‖Analysis.triangularMellinFunction a (Complex.I * t)‖ *
          Real.cos (v * t)) =
      ∑' n : ℕ,
        -(Real.pi / (4 * (b + n) ^ 2)) * Real.exp (-(2 * (b + n)) * (v - 2 * a)) *
          (1 - Real.exp (-(4 * a * (b + n)))) ^ 2 := by
  let F := fun n : ℕ ↦ fun t : ℝ ↦
    (1 / 2 : ℝ) * ((t / 2) ^ 2 / ((b + n) * ((b + n) ^ 2 + (t / 2) ^ 2))) *
      ‖Analysis.triangularMellinFunction a (Complex.I * t)‖
  have hp (n : ℕ) : 0 < b + n := add_pos_of_pos_of_nonneg hb (Nat.cast_nonneg n)
  have hF0 (n : ℕ) (t : ℝ) : 0 ≤ F n t := by
    exact
      mul_nonneg
        (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 1 / 2)
          (div_nonneg (sq_nonneg _)
            (mul_nonneg (hp n).le (add_nonneg (sq_nonneg _) (sq_nonneg _)))))
        (norm_nonneg _)
  have hf (n : ℕ) : MeasureTheory.Integrable (F n) :=
    (Analysis.triangular_digamma_integrable_and_bound ha.ne' (hp n)).1
  have hbound (n : ℕ) : (∫ t : ℝ, F n t) ≤ Real.pi * ((b + n) ^ 2)⁻¹ :=
    (Analysis.triangular_digamma_integrable_and_bound ha.ne' (hp n)).2
  let G (n : ℕ) (t : ℝ) := F n t * Real.cos (v * t)
  have hg (n : ℕ) (t : ℝ) : ‖G n t‖ ≤ F n t := by
    unfold G
    rw [norm_mul, Real.norm_of_nonneg (hF0 n t), Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (hF0 n t)).trans_eq (mul_one _)
  have hi (n : ℕ) : MeasureTheory.Integrable (G n) := by
    apply (hf n).mono' ((hf n).aestronglyMeasurable.mul (by fun_prop))
    exact Filter.Eventually.of_forall (hg n)
  have hs := (Analysis.summable_shifted_inverse_squares hb).mul_left Real.pi
  have hsum :=
    hs.of_nonneg_of_le (fun n => MeasureTheory.integral_nonneg (fun t : ℝ => norm_nonneg (G n t)))
      (fun n => (MeasureTheory.integral_mono (hi n).norm (hf n) (hg n)).trans (hbound n))
  have he := MeasureTheory.integral_tsum_of_summable_integral_norm hi hsum
  have hpoint (t : ℝ) :
    (∑' n : ℕ, F n t) =
      (1 / 2 : ℝ) *
        ((Complex.digamma ((b : ℂ) + Complex.I * (t / 2))).re - (Complex.digamma (b : ℂ)).re) *
        ‖Analysis.triangularMellinFunction a (Complex.I * t)‖ := by
    dsimp only [F]
    rw [tsum_mul_right, tsum_mul_left, ←
      AnalyticNumberTheory.Gamma.digamma_vertical_re_sub_eq_tsum hb]
    simp only [Complex.ofReal_div, Complex.ofReal_ofNat]
  have hmod (t : ℝ) :
    (∑' n : ℕ, G n t) =
      (1 / 2 : ℝ) *
        ((Complex.digamma ((b : ℂ) + Complex.I * (t / 2))).re - (Complex.digamma (b : ℂ)).re) *
        ‖Analysis.triangularMellinFunction a (Complex.I * t)‖ *
        Real.cos (v * t) := by
    unfold G
    rw [tsum_mul_right, hpoint]
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hmod)] at he
  rw [← he]
  exact tsum_congr (fun n => triangle_translated_pole ha (hp n) hv)

end PseudoPrime.PrimeTestBounds.MillerRabin
