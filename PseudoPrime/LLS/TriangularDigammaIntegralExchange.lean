/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TriangularResolventFirstMoment
public import PseudoPrime.AnalyticNumberTheory.Gamma.EulerLogSeries

/-! # Integrated absolute convergence of the vertical digamma series -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For real coordinate and height, the complex norm is the square root of
the sum of their squares. Compute real and imaginary parts. This supports resolvent norms. -/
theorem norm_real_add_I_mul_eq_sqrt (c t : ℝ) :
    ‖(c : ℂ) + Complex.I * t‖ = Real.sqrt (c ^ 2 + t ^ 2) := by
  rw [Complex.norm_def, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, mul_zero, one_mul, sub_zero, zero_add,
    add_zero]
  congr 1
  ring

/-- For positive real c and real height, the reciprocal difference norm is
abs(t)/(c*sqrt(c^2+t^2)). Subtract the reciprocals with nonzero denominators and take norms.
This preserves height decay when bounding the integrated digamma series. -/
theorem vertical_resolvent_norm {c : ℝ} (hc : 0 < c) (t : ℝ) :
    ‖1 / (c : ℂ) - 1 / ((c : ℂ) + Complex.I * t)‖ = |t| / (c * Real.sqrt (c ^ 2 + t ^ 2)) := by
  have hr : 0 < ((c : ℂ) + Complex.I * t).re := by
    simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero] using hc
  have hz : (c : ℂ) + Complex.I * t ≠ 0 := by
    simpa only [Nat.cast_zero, neg_zero] using AnalyticNumberTheory.Gamma.not_neg_nat_of_re_pos hr 0
  rw [div_sub_div 1 1 (Complex.ofReal_ne_zero.mpr hc.ne') hz]
  simp only [one_mul, mul_one, add_sub_cancel_left]
  rw [norm_div, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs t, Real.norm_eq_abs c, abs_of_pos hc, one_mul, norm_real_add_I_mul_eq_sqrt]

/-- For positive real c and real height, compute the reciprocal difference
at half height with denominator c*sqrt((2c)^2+t^2). Rescale the norm identity.
This matches the Gamma-factor digamma argument on the central line. -/
theorem vertical_half_height_resolvent_norm {c : ℝ} (hc : 0 < c) (t : ℝ) :
    ‖1 / (c : ℂ) - 1 / ((c : ℂ) + Complex.I * (t / 2))‖ =
      |t| / (c * Real.sqrt ((2 * c) ^ 2 + t ^ 2)) := by
  have hcast : (t : ℂ) / 2 = ((t / 2 : ℝ) : ℂ) := by rw [Complex.ofReal_div, Complex.ofReal_ofNat]
  rw [hcast, vertical_resolvent_norm hc]
  have he : c ^ 2 + (t / 2) ^ 2 = ((2 * c) ^ 2 + t ^ 2) / 4 := by ring
  have hd : 0 < (2 * c) ^ 2 + t ^ 2 :=
    add_pos_of_pos_of_nonneg (sq_pos_of_pos (mul_pos (by norm_num only) hc)) (sq_nonneg t)
  rw [he, Real.sqrt_div hd.le, abs_div]
  norm_num only [abs_of_pos (by norm_num only : (0 : ℝ) < 2)]
  apply
    (div_eq_div_iff (mul_pos hc (div_pos (Real.sqrt_pos.mpr hd) (by norm_num only))).ne'
        (mul_pos hc (Real.sqrt_pos.mpr hd)).ne').mpr
  ring

/-- For positive a, c and scale x, the vertical half-height reciprocal term,
weighted by the triangular kernel and Mellin phase, has integrable norm. Its normalized
integral is at most (2a+2)/(c*sqrt(2c)). The phase has unit norm; apply the first-moment bound.
This supplies inverse three-half-power decay in the shifted pole. -/
theorem triangular_vertical_resolvent_norm_integrable_and_bound {a c x : ℝ} (ha : 0 < a)
    (hc : 0 < c) (hx : 0 < x) :
    MeasureTheory.Integrable
        (fun t : ℝ ↦
          ‖(1 / (c : ℂ) - 1 / ((c : ℂ) + Complex.I * (t / 2))) *
              Analysis.triangularMellinFunction a (Complex.I * t) *
              (x : ℂ) ^ (Complex.I * t)‖) ∧
      (∫ t : ℝ,
            ‖(1 / (c : ℂ) - 1 / ((c : ℂ) + Complex.I * (t / 2))) *
                Analysis.triangularMellinFunction a (Complex.I * t) *
                (x : ℂ) ^ (Complex.I * t)‖) /
          (2 * Real.pi) ≤
        (2 * a + 2) / (c * Real.sqrt (2 * c)) := by
  let F := fun t : ℝ ↦
    |t| * ‖Analysis.triangularMellinFunction a (Complex.I * t)‖ / Real.sqrt ((2 * c) ^ 2 + t ^ 2)
  have hc2 : 0 < 2 * c := mul_pos (by norm_num only) hc
  have hI := (triangular_resolvent_first_moment_integrable_and_bound ha hc2).1
  have hb := triangular_resolvent_normalized_first_moment_le ha hc2
  change MeasureTheory.Integrable F at hI
  change (∫ t : ℝ, F t) / (2 * Real.pi) ≤ (2 * a + 2) / Real.sqrt (2 * c) at hb
  have he (t : ℝ) :
    ‖(1 / (c : ℂ) - 1 / ((c : ℂ) + Complex.I * (t / 2))) *
          Analysis.triangularMellinFunction a (Complex.I * t) *
          (x : ℂ) ^ (Complex.I * t)‖ =
      (1 / c) * F t := by
    rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, mul_zero, sub_zero, Real.rpow_zero, mul_one]
    rw [vertical_half_height_resolvent_norm hc]
    dsimp only [F]
    ring
  have hi := (hI.const_mul (1 / c)).congr (MeasureTheory.ae_of_all _ (fun t ↦ (he t).symm))
  refine ⟨hi, ?_⟩
  rw [MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ he),
    MeasureTheory.integral_const_mul, mul_div_assoc]
  have h := mul_le_mul_of_nonneg_left hb (one_div_nonneg.mpr hc.le)
  exact h.trans_eq (by ring)

/-- For positive a, b and x, the normalized integrated norms of the shifted
vertical reciprocal differences are summable. Compare positive indices with a three-half
p-series using the moment bound; the zero term is a finite exception.
This is the absolute convergence needed for exchanging series and integration. -/
theorem summable_triangular_vertical_resolvent_integral_norm {a b x : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hx : 0 < x) :
    Summable
      (fun n : ℕ ↦
        (∫ t : ℝ,
            ‖(1 / ((b + n : ℝ) : ℂ) - 1 / (((b + n : ℝ) : ℂ) + Complex.I * (t / 2))) *
                Analysis.triangularMellinFunction a (Complex.I * t) *
                (x : ℂ) ^ (Complex.I * t)‖) /
          (2 * Real.pi)) := by
  have hs : Summable (fun n : ℕ ↦ ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹) :=
    Real.summable_nat_rpow_inv.mpr (by norm_num only)
  apply (hs.mul_left (2 * a + 2)).of_norm_bounded_eventually_nat
  apply Nat.eventually_pos.mono
  intro n hn
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hc : 0 < b + n := add_pos_of_pos_of_nonneg hb (Nat.cast_nonneg n)
  have h := (triangular_vertical_resolvent_norm_integrable_and_bound ha hc hx).2
  have hi :
    0 ≤
      (∫ t : ℝ,
          ‖(1 / ((b + n : ℝ) : ℂ) - 1 / (((b + n : ℝ) : ℂ) + Complex.I * (t / 2))) *
              Analysis.triangularMellinFunction a (Complex.I * t) *
              (x : ℂ) ^ (Complex.I * t)‖) /
        (2 * Real.pi) :=
    div_nonneg (MeasureTheory.integral_nonneg (fun _ ↦ norm_nonneg _))
      (mul_pos (by norm_num only) Real.pi_pos).le
  rw [Real.norm_eq_abs, abs_of_nonneg hi]
  have hc1 : (n : ℝ) ≤ b + n := by linarith only [hb]
  have hc2 : (n : ℝ) ≤ 2 * (b + n) := by linarith only [hb, hn0]
  have hd := mul_le_mul hc1 (Real.sqrt_le_sqrt hc2) (Real.sqrt_nonneg (n : ℝ)) hc.le
  have hp : 0 < (n : ℝ) * Real.sqrt n := mul_pos hn0 (Real.sqrt_pos.mpr hn0)
  have hB := div_le_div_of_nonneg_left (by linarith only [ha] : 0 ≤ 2 * a + 2) hp hd
  have he : (n : ℝ) ^ (3 / 2 : ℝ) = (n : ℝ) * Real.sqrt n := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num only, Real.rpow_add hn0, Real.rpow_one, ←
      Real.sqrt_eq_rpow]
  rw [← he] at hB
  exact h.trans (by simpa only [div_eq_mul_inv] using hB)

/-- For positive parameter, pole coordinate and scale, the complex vertical
reciprocal term weighted by the triangular kernel and phase is integrable.
Its continuous factors are measurable and its norm is integrable. This supplies each
term's integrability in the digamma series-integral exchange. -/
theorem integrable_triangular_vertical_resolvent {a c x : ℝ} (ha : 0 < a) (hc : 0 < c)
    (hx : 0 < x) :
    MeasureTheory.Integrable
      (fun t : ℝ ↦
        (1 / (c : ℂ) - 1 / ((c : ℂ) + Complex.I * (t / 2))) *
          Analysis.triangularMellinFunction a (Complex.I * t) *
          (x : ℂ) ^ (Complex.I * t)) := by
  have hn (t : ℝ) : (c : ℂ) + Complex.I * (t / 2) ≠ 0 := by
    have hr : 0 < ((c : ℂ) + Complex.I * (t / 2)).re := by
      simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        zero_mul, Complex.div_ofNat_im, Complex.ofReal_im, zero_div, mul_zero, sub_zero,
        add_zero] using hc
    simpa only [Nat.cast_zero, neg_zero] using AnalyticNumberTheory.Gamma.not_neg_nat_of_re_pos hr 0
  have hD : Continuous (fun t : ℝ ↦ 1 / (c : ℂ) - 1 / ((c : ℂ) + Complex.I * (t / 2))) :=
    continuous_const.sub
      (continuous_const.div
        (continuous_const.add (continuous_const.mul (Complex.continuous_ofReal.div_const 2))) hn)
  have hK : Continuous (fun t : ℝ ↦ Analysis.triangularMellinFunction a (Complex.I * t)) :=
    (Analysis.differentiable_triangularMellinFunction a).continuous.comp
      (continuous_const.mul Complex.continuous_ofReal)
  have hP : Continuous (fun t : ℝ ↦ (x : ℂ) ^ (Complex.I * t)) :=
    (continuous_const.mul Complex.continuous_ofReal).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))
  exact
    (MeasureTheory.integrable_norm_iff ((hD.mul hK).mul hP).aestronglyMeasurable).mp
      (triangular_vertical_resolvent_norm_integrable_and_bound ha hc hx).1

/-- For positive triangular parameter, real digamma base and scale, integrate
the weighted vertical digamma difference term by term. Use the complex reciprocal-series
identity and summable integrated norms. The Mellin phase is retained, and no GRH is needed.
This connects scalar resolvent inversion to the signed Gamma integral. -/
theorem integral_triangular_digamma_vertical_sub_eq_tsum {a b x : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hx : 0 < x) :
    (∫ t : ℝ,
        (Complex.digamma ((b : ℂ) + Complex.I * (t / 2)) - Complex.digamma (b : ℂ)) *
          Analysis.triangularMellinFunction a (Complex.I * t) *
          (x : ℂ) ^ (Complex.I * t)) =
      ∑' n : ℕ,
        ∫ t : ℝ,
          (1 / ((b + n : ℝ) : ℂ) - 1 / (((b + n : ℝ) : ℂ) + Complex.I * (t / 2))) *
            Analysis.triangularMellinFunction a (Complex.I * t) *
            (x : ℂ) ^ (Complex.I * t) := by
  let F := fun (n : ℕ) (t : ℝ) ↦
    (1 / ((b + n : ℝ) : ℂ) - 1 / (((b + n : ℝ) : ℂ) + Complex.I * (t / 2))) *
      Analysis.triangularMellinFunction a (Complex.I * t) *
      (x : ℂ) ^ (Complex.I * t)
  have hs := (summable_triangular_vertical_resolvent_integral_norm ha hb hx).mul_left (2 * Real.pi)
  simp only [mul_div_cancel₀ _ (mul_pos (by norm_num only : (0 : ℝ) < 2) Real.pi_pos).ne'] at hs
  change Summable (fun n : ℕ ↦ ∫ t : ℝ, ‖F n t‖) at hs
  have hi (n : ℕ) : MeasureTheory.Integrable (F n) :=
    integrable_triangular_vertical_resolvent ha (add_pos_of_pos_of_nonneg hb (Nat.cast_nonneg n)) hx
  have he (t : ℝ) :
    (Complex.digamma ((b : ℂ) + Complex.I * (t / 2)) - Complex.digamma (b : ℂ)) *
        Analysis.triangularMellinFunction a (Complex.I * t) *
        (x : ℂ) ^ (Complex.I * t) =
      ∑' n : ℕ, F n t := by
    have hr : 0 < ((b : ℂ) + Complex.I * (t / 2)).re := by
      simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        zero_mul, Complex.div_ofNat_im, Complex.ofReal_im, zero_div, mul_zero, sub_zero,
        add_zero] using hb
    rw [AnalyticNumberTheory.Gamma.digamma_sub_eq_resolventSeries hr
        (by simpa only [Complex.ofReal_re] using hb),
      ← tsum_mul_right, ← tsum_mul_right]
    apply tsum_congr
    intro n
    dsimp only [F]
    simp only [Complex.ofReal_add, Complex.ofReal_natCast]
    ring
  rw [MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ he)]
  exact (MeasureTheory.integral_tsum_of_summable_integral_norm hi hs).symm

end PseudoPrime.LLS.PaperStatements
