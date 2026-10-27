/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TriangularDigammaIntegralExchange

/-! # First-moment domination for weighted digamma resolvents

Use the quadratic pole-coordinate decay before exchanging the Gamma-weighted series.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Input: positive pole coordinate c and arbitrary real height t.
Claim: the half-height reciprocal difference norm is at most abs(t)/(2c^2).
Proof: bound its exact denominator below using the positive real coordinate.
Role: summable pole-coordinate domination for kernels with an integrable first moment. -/
theorem vertical_half_height_resolvent_norm_le_first_moment {c : ℝ} (hc : 0 < c) (t : ℝ) :
    ‖1 / (c : ℂ) - 1 / ((c : ℂ) + Complex.I * (t / 2))‖ ≤ |t| / (2 * c ^ 2) := by
  rw [vertical_half_height_resolvent_norm hc]
  have hs : 2 * c ≤ Real.sqrt ((2 * c) ^ 2 + t ^ 2) := by
    nlinarith only [Real.sq_sqrt (add_nonneg (sq_nonneg (2 * c)) (sq_nonneg t)),
      Real.sqrt_nonneg ((2 * c) ^ 2 + t ^ 2), sq_nonneg t]
  have hb :=
    div_le_div_of_nonneg_left (abs_nonneg t)
      (mul_pos hc (mul_pos (by norm_num only : (0 : ℝ) < 2) hc))
      (mul_le_mul_of_nonneg_left hs hc.le)
  convert hb using 1
  ring

/-- Input: a positive pole coordinate and any complex weight at each height.
Claim: the weighted reciprocal difference norm is bounded by the weighted first moment.
Proof: multiply the uniform reciprocal estimate by the nonnegative weight norm.
Role: common pointwise majorant for Gamma-weighted series integration. -/
theorem norm_weighted_vertical_resolvent_le_first_moment {c : ℝ} (hc : 0 < c) (W : ℝ → ℂ) (t : ℝ) :
    ‖(1 / (c : ℂ) - 1 / ((c : ℂ) + Complex.I * (t / 2))) * W t‖ ≤
      (1 / (2 * c ^ 2)) * (|t| * ‖W t‖) := by
  rw [norm_mul]
  have h :=
    mul_le_mul_of_nonneg_right (vertical_half_height_resolvent_norm_le_first_moment hc t)
      (norm_nonneg (W t))
  convert h using 1
  ring

/-- Input: a measurable complex weight whose norm has an integrable first moment.
Claim: every positive-coordinate weighted reciprocal difference is integrable.
Proof: continuity of the pole-free factor and first-moment domination.
Role: justify each term in the Gamma digamma series exchange. -/
theorem integrable_weighted_vertical_resolvent {c : ℝ} (hc : 0 < c) (W : ℝ → ℂ)
    (hW : MeasureTheory.AEStronglyMeasurable W MeasureTheory.volume)
    (hM : MeasureTheory.Integrable (fun t : ℝ ↦ |t| * ‖W t‖)) :
    MeasureTheory.Integrable
      (fun t : ℝ ↦ (1 / (c : ℂ) - 1 / ((c : ℂ) + Complex.I * (t / 2))) * W t) := by
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
  exact
    (hM.const_mul (1 / (2 * c ^ 2))).mono' (hD.aestronglyMeasurable.mul hW)
      (MeasureTheory.ae_of_all _ (norm_weighted_vertical_resolvent_le_first_moment hc W))

/-- Input: a measurable weight with integrable absolute first moment and positive coordinate.
Claim: the integrated reciprocal-term norm is bounded by the first moment divided by 2c^2.
Proof: integrate the pointwise majorant using the proved term integrability.
Role: quantitative bound for summing the digamma terms before integration. -/
theorem integral_norm_weighted_vertical_resolvent_le {c : ℝ} (hc : 0 < c) (W : ℝ → ℂ)
    (hW : MeasureTheory.AEStronglyMeasurable W MeasureTheory.volume)
    (hM : MeasureTheory.Integrable (fun t : ℝ ↦ |t| * ‖W t‖)) :
    (∫ t : ℝ, ‖(1 / (c : ℂ) - 1 / ((c : ℂ) + Complex.I * (t / 2))) * W t‖) ≤
      (1 / (2 * c ^ 2)) * (∫ t : ℝ, |t| * ‖W t‖) := by
  have hi := (integrable_weighted_vertical_resolvent hc W hW hM).norm
  have hb :=
    MeasureTheory.integral_mono hi (hM.const_mul (1 / (2 * c ^ 2)))
      (norm_weighted_vertical_resolvent_le_first_moment hc W)
  simpa only [MeasureTheory.integral_const_mul] using hb

/-- Input: positive digamma base and a measurable weight with integrable first moment.
Claim: the integrated norms of all weighted reciprocal differences form a summable series.
Proof: dominate the nth term by a constant times n to the power minus two for positive n.
Role: justify exchanging the signed digamma series with the weighted integral. -/
theorem summable_weighted_vertical_resolvent_integral_norm {b : ℝ} (hb : 0 < b) (W : ℝ → ℂ)
    (hW : MeasureTheory.AEStronglyMeasurable W MeasureTheory.volume)
    (hM : MeasureTheory.Integrable (fun t : ℝ ↦ |t| * ‖W t‖)) :
    Summable
      (fun n : ℕ ↦
        ∫ t : ℝ,
          ‖(1 / ((b + n : ℝ) : ℂ) - 1 / (((b + n : ℝ) : ℂ) + Complex.I * (t / 2))) * W t‖) := by
  let M := ∫ t : ℝ, |t| * ‖W t‖
  have hM0 : 0 ≤ M :=
    MeasureTheory.integral_nonneg (fun t ↦ mul_nonneg (abs_nonneg t) (norm_nonneg (W t)))
  have hs : Summable (fun n : ℕ ↦ ((n : ℝ) ^ (2 : ℝ))⁻¹) :=
    Real.summable_nat_rpow_inv.mpr (by norm_num only)
  apply (hs.mul_left (M / 2)).of_norm_bounded_eventually_nat
  filter_upwards [Filter.eventually_gt_atTop (0 : ℕ)] with n hn
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
  have hc : 0 < b + (n : ℝ) := add_pos_of_pos_of_nonneg hb (Nat.cast_nonneg n)
  have hBound := integral_norm_weighted_vertical_resolvent_le hc W hW hM
  rw [Real.norm_eq_abs, abs_of_nonneg (MeasureTheory.integral_nonneg (fun _ ↦ norm_nonneg _))]
  have hden : 2 * (n : ℝ) ^ 2 ≤ 2 * (b + n) ^ 2 := by
    nlinarith only [mul_nonneg hb.le hn0.le, sq_nonneg b]
  have hDiv :=
    div_le_div_of_nonneg_left hM0 (mul_pos (by norm_num only : (0 : ℝ) < 2) (sq_pos_of_pos hn0))
      hden
  calc
    _ ≤ (1 / (2 * (b + n) ^ 2)) * M := hBound
    _ = M / (2 * (b + n) ^ 2) := by ring
    _ ≤ M / (2 * (n : ℝ) ^ 2) := hDiv
    _ = (M / 2) * ((n : ℝ) ^ (2 : ℝ))⁻¹ := by
      rw [Real.rpow_two]; ring

/-- Input: positive digamma base and a measurable weight with integrable first moment.
Claim: the weighted vertical digamma difference may be integrated term by term.
Proof: retain the reciprocal differences and use summable integrated norms.
Role: kernel-independent exchange theorem for the Gamma archimedean series. -/
theorem integral_weighted_digamma_vertical_sub_eq_tsum {b : ℝ} (hb : 0 < b) (W : ℝ → ℂ)
    (hW : MeasureTheory.AEStronglyMeasurable W MeasureTheory.volume)
    (hM : MeasureTheory.Integrable (fun t : ℝ ↦ |t| * ‖W t‖)) :
    (∫ t : ℝ, (Complex.digamma ((b : ℂ) + Complex.I * (t / 2)) - Complex.digamma (b : ℂ)) * W t) =
      ∑' n : ℕ,
        ∫ t : ℝ, (1 / ((b + n : ℝ) : ℂ) - 1 / (((b + n : ℝ) : ℂ) + Complex.I * (t / 2))) * W t := by
  let F := fun (n : ℕ) (t : ℝ) ↦
    (1 / ((b + n : ℝ) : ℂ) - 1 / (((b + n : ℝ) : ℂ) + Complex.I * (t / 2))) * W t
  have hs := summable_weighted_vertical_resolvent_integral_norm hb W hW hM
  have hi (n : ℕ) : MeasureTheory.Integrable (F n) :=
    integrable_weighted_vertical_resolvent (add_pos_of_pos_of_nonneg hb (Nat.cast_nonneg n)) W hW hM
  have he (t : ℝ) :
    (Complex.digamma ((b : ℂ) + Complex.I * (t / 2)) - Complex.digamma (b : ℂ)) * W t =
      ∑' n : ℕ, F n t := by
    have hr : 0 < ((b : ℂ) + Complex.I * (t / 2)).re := by
      simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        zero_mul, Complex.div_ofNat_im, Complex.ofReal_im, zero_div, mul_zero, sub_zero,
        add_zero] using hb
    rw [AnalyticNumberTheory.Gamma.digamma_sub_eq_resolventSeries hr
        (by simpa only [Complex.ofReal_re] using hb),
      ← tsum_mul_right]
    apply tsum_congr
    intro n
    dsimp only [F]
    simp only [Complex.ofReal_add, Complex.ofReal_natCast]
    ring
  rw [MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ he)]
  exact (MeasureTheory.integral_tsum_of_summable_integral_norm hi hs).symm

end PseudoPrime.LLS.PaperStatements
