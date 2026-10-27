/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ReciprocalGapReflectedResolvent
public import PseudoPrime.AnalyticNumberTheory.General.IntegrableComplexSeries

/-! # Exact reflected digamma integration between adjustable rational poles -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For positive digamma base and continuous quadratic-decay weight, exchange the
reflected digamma difference with the series of weighted reciprocal differences.
Reflect the existing positive-height exchange through measure-preserving negation.
This retains signs for the left-contour Gamma contribution. -/
theorem integral_quadratic_weight_reflected_digamma_sub_eq_tsum {A b : ℝ} (hb : 0 < b) (W : ℝ → ℂ)
    (hW : Continuous W) (hbound : ∀ t : ℝ, ‖W t‖ ≤ A / (1 + t ^ 2)) :
    (∫ t : ℝ, (Complex.digamma ((b : ℂ) - Complex.I * (t / 2)) - Complex.digamma (b : ℂ)) * W t) =
      ∑' n : ℕ,
        ∫ t : ℝ, (1 / ((b + n : ℝ) : ℂ) - 1 / (((b + n : ℝ) : ℂ) - Complex.I * (t / 2))) * W t := by
  have he :=
    integral_quadratic_weight_digamma_vertical_sub_eq_tsum hb (fun t ↦ W (-t))
      (hW.comp continuous_neg) (fun t ↦ by simpa only [neg_sq] using hbound (-t))
  have hI :=
    MeasureTheory.integral_neg_eq_self
      (fun t : ℝ ↦
        (Complex.digamma ((b : ℂ) + Complex.I * (t / 2)) - Complex.digamma (b : ℂ)) * W (-t))
      MeasureTheory.volume
  simp only [neg_div, Complex.ofReal_neg, mul_neg, neg_neg, ← sub_eq_add_neg] at hI
  rw [hI, he]
  apply tsum_congr
  intro n
  have hn :=
    MeasureTheory.integral_neg_eq_self
      (fun t : ℝ ↦ (1 / ((b + n : ℝ) : ℂ) - 1 / (((b + n : ℝ) : ℂ) + Complex.I * (t / 2))) * W (-t))
      MeasureTheory.volume
  simpa only [neg_div, Complex.ofReal_neg, mul_neg, neg_neg, ← sub_eq_add_neg] using hn.symm

/-- For positive digamma base and continuous quadratic-decay weight, the full weighted
reflected digamma difference is integrable. Reflect the term estimates and use summable
integral norms to prove integrability of the pointwise complex series.
No separate first-moment or convergence premise is imposed on the weight. -/
theorem integrable_quadratic_weight_reflected_digamma_sub {A b : ℝ} (hb : 0 < b) (W : ℝ → ℂ)
    (hW : Continuous W) (hbound : ∀ t : ℝ, ‖W t‖ ≤ A / (1 + t ^ 2)) :
    MeasureTheory.Integrable
      (fun t : ℝ ↦
        (Complex.digamma ((b : ℂ) - Complex.I * (t / 2)) - Complex.digamma (b : ℂ)) * W t) := by
  let V := fun t : ℝ ↦ W (-t)
  let F := fun (n : ℕ) (t : ℝ) ↦
    (1 / ((b + n : ℝ) : ℂ) - 1 / (((b + n : ℝ) : ℂ) - Complex.I * (t / 2))) * W t
  have hV : Continuous V := hW.comp continuous_neg
  have hv (t : ℝ) : ‖V t‖ ≤ A / (1 + t ^ 2) := by simpa only [V, neg_sq] using hbound (-t)
  have hi (n : ℕ) : MeasureTheory.Integrable (F n) := by
    have h :=
      (quadratic_weight_vertical_resolvent_integral_bound
          (add_pos_of_pos_of_nonneg hb (Nat.cast_nonneg n)) V hV hv).1.comp_neg
    simpa only [F, V, neg_div, Complex.ofReal_neg, mul_neg, neg_neg, ← sub_eq_add_neg] using h
  have hs0 := (summable_quadratic_weight_resolvent_integral_norm hb V hV hv).mul_left (2 * Real.pi)
  simp only [mul_div_cancel₀ _ (mul_pos (by norm_num only : (0 : ℝ) < 2) Real.pi_pos).ne'] at hs0
  have hs : Summable (fun n : ℕ ↦ ∫ t : ℝ, ‖F n t‖) := by
    apply hs0.congr
    intro n
    have he :=
      MeasureTheory.integral_neg_eq_self
        (fun t : ℝ ↦
          ‖(1 / ((b + n : ℝ) : ℂ) - 1 / (((b + n : ℝ) : ℂ) + Complex.I * (t / 2))) * V t‖)
        MeasureTheory.volume
    simpa only [F, V, neg_div, Complex.ofReal_neg, mul_neg, neg_neg, ← sub_eq_add_neg] using he.symm
  have he (t : ℝ) :
    (Complex.digamma ((b : ℂ) - Complex.I * (t / 2)) - Complex.digamma (b : ℂ)) * W t =
      ∑' n : ℕ, F n t := by
    have hr : 0 < ((b : ℂ) - Complex.I * (t / 2)).re := by
      simpa only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        zero_mul, Complex.div_ofNat_im, Complex.ofReal_im, zero_div, mul_zero, sub_zero] using hb
    rw [AnalyticNumberTheory.Gamma.digamma_sub_eq_resolventSeries hr
        (by simpa only [Complex.ofReal_re] using hb),
      ← tsum_mul_right]
    apply tsum_congr
    intro n
    dsimp only [F]
    simp only [Complex.ofReal_add, Complex.ofReal_natCast]
    ring
  exact
    (AnalyticNumberTheory.General.integrable_complex_tsum_of_summable_integral_norm hi hs).congr
      (MeasureTheory.ae_of_all _ (fun t ↦ (he t).symm))

/-- For positive gap and digamma base, a line between the poles and x>=1, evaluate the
normalized weighted reciprocal difference exactly. Subtract two integrable terms and
use the reflected resolvent formula. This supplies each scalar term of the digamma series. -/
theorem reciprocalGap_reflected_difference_integral {h c b x : ℝ} (hh : 0 < h)
    (hcl : -1 / 2 - h < c) (hcu : c < -1 / 2) (hx : 1 ≤ x) (hb : 0 < b) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          (1 / (b : ℂ) - 1 / ((b : ℂ) - Complex.I * (t / 2))) * reciprocalGapMiddleWeight h c x t) =
      ((-x ^ (-1 / 2 - h) / h : ℝ) : ℂ) *
        (1 / (b : ℂ) - 1 / ((b + (c + (1 / 2 + h)) / 2 : ℝ) : ℂ)) := by
  let W := reciprocalGapMiddleWeight h c x
  have hx0 := zero_lt_one.trans_le hx
  have hW := continuous_reciprocalGapMiddleWeight hcl hcu hx0
  have hiW := integrable_reciprocalGapMiddleWeight hcl hcu hx0
  obtain ⟨A, hA⟩ := norm_reciprocalGapMiddleWeight_quadratic hcl hcu hx0
  have hiD :
    MeasureTheory.Integrable
      (fun t : ℝ ↦ (1 / (b : ℂ) - 1 / ((b : ℂ) - Complex.I * (t / 2))) * W t) := by
    have h :=
      (quadratic_weight_vertical_resolvent_integral_bound hb (fun t ↦ W (-t))
          (hW.comp continuous_neg) (fun t ↦ by simpa only [neg_sq] using hA (-t))).1.comp_neg
    simpa only [neg_div, Complex.ofReal_neg, mul_neg, neg_neg, ← sub_eq_add_neg] using h
  have hiR : MeasureTheory.Integrable (fun t : ℝ ↦ (1 / ((b : ℂ) - Complex.I * (t / 2))) * W t) :=
    ((hiW.const_mul (1 / (b : ℂ))).sub hiD).congr
      (MeasureTheory.ae_of_all _
        (fun t ↦ by
          change (1 / (b : ℂ)) * W t - (1 / (b : ℂ) - 1 / ((b : ℂ) - Complex.I * (t / 2))) * W t = _
          ring))
  have he (t : ℝ) :
    ((b + c / 2 : ℝ) : ℂ) - ((c : ℂ) + Complex.I * t) / 2 = (b : ℂ) - Complex.I * (t / 2) := by
    push_cast
    ring
  have hR :=
    reciprocalGap_reflected_resolvent_integral hh hcl hcu hx (a := b + c / 2)
      (by linarith only [hb])
  simp only [he] at hR
  have hM := reciprocalGap_left_kernel_integral hh hcl hcu hx
  change ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ, W t) = _ at hM
  change
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ, (1 / (b : ℂ) - 1 / ((b : ℂ) - Complex.I * (t / 2))) * W t) =
      _
  simp only [sub_mul]
  rw [MeasureTheory.integral_sub (hiW.const_mul _) hiR, mul_sub, MeasureTheory.integral_const_mul,
    mul_left_comm, hM, hR]
  push_cast
  have ht : (b : ℂ) + c / 2 + (1 / 2 + h) / 2 = b + ((c : ℂ) + (1 / 2 + h)) / 2 := by ring
  rw [ht]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- For positive gap and base, a line between the poles and x>=1, the normalized reflected
digamma difference integral equals -x^(-1/2-h)/h times the corresponding real-axis
digamma difference. Exchange the series and apply the scalar resolvent evaluations.
This retains the exact signed contribution rather than an absolute Gamma budget. -/
theorem reciprocalGap_reflected_digamma_sub_integral {h c b x : ℝ} (hh : 0 < h)
    (hcl : -1 / 2 - h < c) (hcu : c < -1 / 2) (hx : 1 ≤ x) (hb : 0 < b) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          (Complex.digamma ((b : ℂ) - Complex.I * (t / 2)) - Complex.digamma (b : ℂ)) *
            reciprocalGapMiddleWeight h c x t) =
      ((-x ^ (-1 / 2 - h) / h : ℝ) : ℂ) *
        (Complex.digamma ((b + (c + (1 / 2 + h)) / 2 : ℝ) : ℂ) - Complex.digamma (b : ℂ)) := by
  have hx0 := zero_lt_one.trans_le hx
  obtain ⟨A, hA⟩ := norm_reciprocalGapMiddleWeight_quadratic hcl hcu hx0
  rw [integral_quadratic_weight_reflected_digamma_sub_eq_tsum hb (reciprocalGapMiddleWeight h c x)
      (continuous_reciprocalGapMiddleWeight hcl hcu hx0) hA,
    ← tsum_mul_left]
  have ht : 0 < (((b + (c + (1 / 2 + h)) / 2 : ℝ) : ℂ)).re := by
    rw [Complex.ofReal_re]
    linarith only [hb, hcl]
  rw [AnalyticNumberTheory.Gamma.digamma_sub_eq_resolventSeries ht
      (by simpa only [Complex.ofReal_re] using hb),
    ← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [reciprocalGap_reflected_difference_integral hh hcl hcu hx
      (add_pos_of_pos_of_nonneg hb (Nat.cast_nonneg n))]
  have he :
    ((b + n + (c + (1 / 2 + h)) / 2 : ℝ) : ℂ) = ((b + (c + (1 / 2 + h)) / 2 : ℝ) : ℂ) + n := by
    push_cast; ring
  rw [he]
  simp only [Complex.ofReal_add, Complex.ofReal_natCast]

/-- For positive gap and base, a line between the poles and x>=1, integrate the full
weighted reflected digamma function exactly at the shifted positive real argument.
Restore its integrable constant baseline after evaluating the difference series.
This is the parity-independent scalar identity needed for Gamma-factor inversion. -/
theorem reciprocalGap_reflected_digamma_integral {h c b x : ℝ} (hh : 0 < h) (hcl : -1 / 2 - h < c)
    (hcu : c < -1 / 2) (hx : 1 ≤ x) (hb : 0 < b) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          Complex.digamma ((b : ℂ) - Complex.I * (t / 2)) * reciprocalGapMiddleWeight h c x t) =
      ((-x ^ (-1 / 2 - h) / h : ℝ) : ℂ) *
        Complex.digamma ((b + (c + (1 / 2 + h)) / 2 : ℝ) : ℂ) := by
  have hx0 := zero_lt_one.trans_le hx
  let W := reciprocalGapMiddleWeight h c x
  have hiW := integrable_reciprocalGapMiddleWeight hcl hcu hx0
  obtain ⟨A, hA⟩ := norm_reciprocalGapMiddleWeight_quadratic hcl hcu hx0
  have hiD :=
    integrable_quadratic_weight_reflected_digamma_sub hb W
      (continuous_reciprocalGapMiddleWeight hcl hcu hx0) hA
  have he (t : ℝ) :
    Complex.digamma ((b : ℂ) - Complex.I * (t / 2)) * W t =
      (Complex.digamma ((b : ℂ) - Complex.I * (t / 2)) - Complex.digamma (b : ℂ)) * W t +
        Complex.digamma (b : ℂ) * W t := by
    ring
  change
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ, Complex.digamma ((b : ℂ) - Complex.I * (t / 2)) * W t) =
      _
  rw [MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ he),
    MeasureTheory.integral_add hiD (hiW.const_mul _), mul_add,
    reciprocalGap_reflected_digamma_sub_integral hh hcl hcu hx hb, MeasureTheory.integral_const_mul,
    mul_left_comm]
  have hM := reciprocalGap_left_kernel_integral hh hcl hcu hx
  change ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ, reciprocalGapMiddleWeight h c x t) = _ at hM
  rw [hM]
  ring

/-- For positive scale and digamma base on a line between the poles, the full weighted
reflected digamma function is integrable. Add the integrable difference and constant
baseline. This justifies splitting the reflected Gamma factor into its two parts. -/
theorem integrable_reciprocalGap_reflected_digamma {h c b x : ℝ} (hcl : -1 / 2 - h < c)
    (hcu : c < -1 / 2) (hx : 0 < x) (hb : 0 < b) :
    MeasureTheory.Integrable
      (fun t : ℝ ↦
        Complex.digamma ((b : ℂ) - Complex.I * (t / 2)) * reciprocalGapMiddleWeight h c x t) := by
  obtain ⟨A, hA⟩ := norm_reciprocalGapMiddleWeight_quadratic hcl hcu hx
  have hD :=
    integrable_quadratic_weight_reflected_digamma_sub hb (reciprocalGapMiddleWeight h c x)
      (continuous_reciprocalGapMiddleWeight hcl hcu hx) hA
  exact
    (hD.add
          ((integrable_reciprocalGapMiddleWeight hcl hcu hx).const_mul
            (Complex.digamma (b : ℂ)))).congr
      (MeasureTheory.ae_of_all _
        (fun t ↦ by
          change
            (Complex.digamma ((b : ℂ) - Complex.I * (t / 2)) - Complex.digamma (b : ℂ)) *
                  reciprocalGapMiddleWeight h c x t +
                Complex.digamma (b : ℂ) * reciprocalGapMiddleWeight h c x t =
              _
          ring))

end PseudoPrime.LLS.PaperStatements
