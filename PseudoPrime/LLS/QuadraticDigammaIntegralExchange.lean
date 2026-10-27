/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TriangularDigammaIntegralExchange

/-! # Digamma integral exchange for continuous weights with quadratic decay -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For a continuous complex weight with norm at most A/(1+t^2) and positive c, its
absolute first resolvent moment is integrable and its normalized integral is at most
A/sqrt(c). Use a scalar quadratic inequality and two integrable Cauchy majorants.
No integrability of the unregularized absolute first moment is assumed. -/
theorem quadratic_weight_resolvent_moment_bound {A c : ℝ} (hc : 0 < c) (W : ℝ → ℂ)
    (hW : Continuous W) (hbound : ∀ t : ℝ, ‖W t‖ ≤ A / (1 + t ^ 2)) :
    MeasureTheory.Integrable (fun t : ℝ ↦ |t| * ‖W t‖ / Real.sqrt (c ^ 2 + t ^ 2)) ∧
      (∫ t : ℝ, |t| * ‖W t‖ / Real.sqrt (c ^ 2 + t ^ 2)) / (2 * Real.pi) ≤ A / Real.sqrt c := by
  let F := fun t : ℝ ↦ |t| * ‖W t‖ / Real.sqrt (c ^ 2 + t ^ 2)
  let G := fun t : ℝ ↦ (A / Real.sqrt c) * (1 + t ^ 2)⁻¹ + (A * Real.sqrt c) * (c ^ 2 + t ^ 2)⁻¹
  have hd (t : ℝ) : 0 < c ^ 2 + t ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos hc) (sq_nonneg t)
  have hb (t : ℝ) : F t ≤ G t := by
    have hm := resolvent_first_moment_am_bound hc (|t| / Real.sqrt (c ^ 2 + t ^ 2))
    rw [div_pow, sq_abs, Real.sq_sqrt (hd t).le] at hm
    have hw := mul_le_mul_of_nonneg_right hm (norm_nonneg (W t))
    have ht : t ^ 2 * ‖W t‖ ≤ A := by
      have h := (le_div_iff₀ (by linarith only [sq_nonneg t] : 0 < 1 + t ^ 2)).mp (hbound t)
      nlinarith only [h, norm_nonneg (W t)]
    have h1 :=
      mul_le_mul_of_nonneg_left (hbound t) (div_nonneg zero_le_one (Real.sqrt_pos.mpr hc).le)
    have h2 :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right ht (hd t).le) (Real.sqrt_nonneg c)
    dsimp only [F, G]
    simp only [div_eq_mul_inv] at hw h1 h2 ⊢
    nlinarith only [hw, h1, h2]
  have hG : MeasureTheory.Integrable G :=
    ((Analysis.integrable_cauchy_of_pos (by norm_num only : (0 : ℝ) < 1)).congr
            (MeasureTheory.ae_of_all _ (fun t ↦ by norm_num only [one_pow]))).const_mul
        _ |>.add
      ((Analysis.integrable_cauchy_of_pos hc).const_mul _)
  have hF : Continuous F :=
    (continuous_abs.mul hW.norm).div ((continuous_const.add (continuous_id.pow 2)).sqrt)
      (fun t ↦ (Real.sqrt_pos.mpr (hd t)).ne')
  have hiF : MeasureTheory.Integrable F :=
    hG.mono' hF.aestronglyMeasurable
      (MeasureTheory.ae_of_all _
        (fun t ↦ by
          rw [Real.norm_eq_abs,
            abs_of_nonneg
              (div_nonneg (mul_nonneg (abs_nonneg t) (norm_nonneg _)) (Real.sqrt_nonneg _))]
          exact hb t))
  have hi := MeasureTheory.integral_mono hiF hG hb
  have hi1 := Analysis.integrable_cauchy_of_pos (by norm_num only : (0 : ℝ) < 1)
  norm_num only [one_pow] at hi1
  dsimp only [G] at hi
  rw [MeasureTheory.integral_add (hi1.const_mul _)
      ((Analysis.integrable_cauchy_of_pos hc).const_mul _),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul] at hi
  have hmass := Analysis.integral_univ_cauchy_of_pos (by norm_num only : (0 : ℝ) < 1)
  norm_num only [one_pow, div_one] at hmass
  rw [hmass, Analysis.integral_univ_cauchy_of_pos hc] at hi
  have hdiv :=
    div_le_div_of_nonneg_right hi (mul_pos (by norm_num only : (0 : ℝ) < 2) Real.pi_pos).le
  refine ⟨hiF, hdiv.trans_eq ?_⟩
  have hs := Real.sq_sqrt hc.le
  field_simp [hc.ne', (Real.sqrt_pos.mpr hc).ne', Real.pi_ne_zero]
  rw [hs]
  ring

/-- For a continuous quadratically decaying weight and c>0, each weighted vertical
reciprocal difference is integrable and its normalized norm integral is at most
A/(c*sqrt(2c)). Apply the exact reciprocal norm and the regularized moment estimate.
This supplies summable decay in the pole coordinate for rational kernels. -/
theorem quadratic_weight_vertical_resolvent_integral_bound {A c : ℝ} (hc : 0 < c) (W : ℝ → ℂ)
    (hW : Continuous W) (hbound : ∀ t : ℝ, ‖W t‖ ≤ A / (1 + t ^ 2)) :
    MeasureTheory.Integrable
        (fun t : ℝ ↦ (1 / (c : ℂ) - 1 / ((c : ℂ) + Complex.I * (t / 2))) * W t) ∧
      (∫ t : ℝ, ‖(1 / (c : ℂ) - 1 / ((c : ℂ) + Complex.I * (t / 2))) * W t‖) / (2 * Real.pi) ≤
        A / (c * Real.sqrt (2 * c)) := by
  let F := fun t : ℝ ↦ |t| * ‖W t‖ / Real.sqrt ((2 * c) ^ 2 + t ^ 2)
  have h :=
    quadratic_weight_resolvent_moment_bound (mul_pos (by norm_num only : (0 : ℝ) < 2) hc) W hW
      hbound
  have he (t : ℝ) :
    ‖(1 / (c : ℂ) - 1 / ((c : ℂ) + Complex.I * (t / 2))) * W t‖ = (1 / c) * F t := by
    rw [norm_mul, vertical_half_height_resolvent_norm hc]
    dsimp only [F]
    ring
  have hi := (h.1.const_mul (1 / c)).congr (MeasureTheory.ae_of_all _ (fun t ↦ (he t).symm))
  have hn (t : ℝ) : (c : ℂ) + Complex.I * (t / 2) ≠ 0 := by
    have hr : 0 < ((c : ℂ) + Complex.I * (t / 2)).re := by
      simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        zero_mul, Complex.div_ofNat_im, Complex.ofReal_im, zero_div, mul_zero, sub_zero,
        add_zero] using hc
    exact ne_of_apply_ne Complex.re (by simpa only [Complex.zero_re] using hr.ne')
  have hD : Continuous (fun t : ℝ ↦ 1 / (c : ℂ) - 1 / ((c : ℂ) + Complex.I * (t / 2))) :=
    continuous_const.sub
      (continuous_const.div
        (continuous_const.add (continuous_const.mul (Complex.continuous_ofReal.div_const 2))) hn)
  refine ⟨(MeasureTheory.integrable_norm_iff (hD.mul hW).aestronglyMeasurable).mp hi, ?_⟩
  rw [MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ he),
    MeasureTheory.integral_const_mul, mul_div_assoc]
  have hb := mul_le_mul_of_nonneg_left h.2 (one_div_nonneg.mpr hc.le)
  exact hb.trans_eq (by ring)

/-- For b>0 and a continuous weight of quadratic decay, the integrated absolute norms
of the shifted reciprocal differences form a summable series.
Compare the n-th term eventually with A/n^(3/2) using the explicit resolvent bound.
This permits exchanging the digamma series and integration without a first-moment premise. -/
theorem summable_quadratic_weight_resolvent_integral_norm {A b : ℝ} (hb : 0 < b) (W : ℝ → ℂ)
    (hW : Continuous W) (hbound : ∀ t : ℝ, ‖W t‖ ≤ A / (1 + t ^ 2)) :
    Summable
      (fun n : ℕ ↦
        (∫ t : ℝ, ‖(1 / ((b + n : ℝ) : ℂ) - 1 / (((b + n : ℝ) : ℂ) + Complex.I * (t / 2))) * W t‖) /
          (2 * Real.pi)) := by
  have hs : Summable (fun n : ℕ ↦ ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹) :=
    Real.summable_nat_rpow_inv.mpr (by norm_num only)
  have hA : 0 ≤ A :=
    (norm_nonneg (W 0)).trans
      (by simpa only [zero_pow (by norm_num only : 2 ≠ 0), add_zero, div_one] using hbound 0)
  apply (hs.mul_left A).of_norm_bounded_eventually_nat
  apply Nat.eventually_pos.mono
  intro n hn
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hc : 0 < b + n := add_pos_of_pos_of_nonneg hb (Nat.cast_nonneg n)
  have h := (quadratic_weight_vertical_resolvent_integral_bound hc W hW hbound).2
  have hi :
    0 ≤
      (∫ t : ℝ, ‖(1 / ((b + n : ℝ) : ℂ) - 1 / (((b + n : ℝ) : ℂ) + Complex.I * (t / 2))) * W t‖) /
        (2 * Real.pi) :=
    div_nonneg (MeasureTheory.integral_nonneg (fun _ ↦ norm_nonneg _))
      (mul_pos (by norm_num only) Real.pi_pos).le
  rw [Real.norm_eq_abs, abs_of_nonneg hi]
  have hc1 : (n : ℝ) ≤ b + n := by linarith only [hb]
  have hc2 : (n : ℝ) ≤ 2 * (b + n) := by linarith only [hb, hn0]
  have hd := mul_le_mul hc1 (Real.sqrt_le_sqrt hc2) (Real.sqrt_nonneg (n : ℝ)) hc.le
  have hp : 0 < (n : ℝ) * Real.sqrt n := mul_pos hn0 (Real.sqrt_pos.mpr hn0)
  have hB := div_le_div_of_nonneg_left hA hp hd
  have he : (n : ℝ) ^ (3 / 2 : ℝ) = (n : ℝ) * Real.sqrt n := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num only, Real.rpow_add hn0, Real.rpow_one, ←
      Real.sqrt_eq_rpow]
  rw [← he] at hB
  exact h.trans (by simpa only [div_eq_mul_inv] using hB)

/-- For positive digamma base b and any continuous quadratically decaying complex weight,
the weighted vertical digamma difference integral equals the series of reciprocal integrals.
Use the exact digamma series and summability of the integrated norms.
This retains signs for compact rational Mellin kernels whose absolute first moment diverges. -/
theorem integral_quadratic_weight_digamma_vertical_sub_eq_tsum {A b : ℝ} (hb : 0 < b) (W : ℝ → ℂ)
    (hW : Continuous W) (hbound : ∀ t : ℝ, ‖W t‖ ≤ A / (1 + t ^ 2)) :
    (∫ t : ℝ, (Complex.digamma ((b : ℂ) + Complex.I * (t / 2)) - Complex.digamma (b : ℂ)) * W t) =
      ∑' n : ℕ,
        ∫ t : ℝ, (1 / ((b + n : ℝ) : ℂ) - 1 / (((b + n : ℝ) : ℂ) + Complex.I * (t / 2))) * W t := by
  let F := fun (n : ℕ) (t : ℝ) ↦
    (1 / ((b + n : ℝ) : ℂ) - 1 / (((b + n : ℝ) : ℂ) + Complex.I * (t / 2))) * W t
  have hs :=
    (summable_quadratic_weight_resolvent_integral_norm hb W hW hbound).mul_left (2 * Real.pi)
  simp only [mul_div_cancel₀ _ (mul_pos (by norm_num only : (0 : ℝ) < 2) Real.pi_pos).ne'] at hs
  change Summable (fun n : ℕ ↦ ∫ t : ℝ, ‖F n t‖) at hs
  have hi (n : ℕ) : MeasureTheory.Integrable (F n) :=
    (quadratic_weight_vertical_resolvent_integral_bound
        (add_pos_of_pos_of_nonneg hb (Nat.cast_nonneg n)) W hW hbound).1
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
