/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ReciprocalGapReflectedEuler
public import PseudoPrime.LLS.ResolventLaplaceWeights

/-! # Reflected Laplace resolvents on the strip between two rational poles -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For positive real decay and a continuous integrable complex weight, the reflected
Laplace product is integrable on the positive half-line times the full height line.
Separate its norm into real exponential decay and the weight norm. This justifies Fubini. -/
theorem integrable_reflected_resolvent_laplace_mul_weight {a : ℝ} (ha : 0 < a) (W : ℝ → ℂ)
    (hW : Continuous W) (hiW : MeasureTheory.Integrable W) :
    MeasureTheory.Integrable
      (fun p : ℝ × ℝ ↦ Complex.exp (-((a : ℂ) - Complex.I * (p.2 : ℂ) / 2) * (p.1 : ℂ)) * W p.2)
      ((MeasureTheory.volume.restrict (Set.Ioi 0)).prod MeasureTheory.volume) := by
  have hC :
    Continuous (fun p : ℝ × ℝ ↦ Complex.exp (-((a : ℂ) - Complex.I * (p.2 : ℂ) / 2) * (p.1 : ℂ))) :=
    ((continuous_const.sub
            ((continuous_const.mul (Complex.continuous_ofReal.comp continuous_snd)).div_const
              (2 : ℂ))).neg.mul
        (Complex.continuous_ofReal.comp continuous_fst)).cexp
  apply
    (MeasureTheory.integrable_norm_iff (hC.mul (hW.comp continuous_snd)).aestronglyMeasurable).mp
  have hR := integrableOn_exp_mul_Ioi (neg_neg_of_pos ha) (0 : ℝ)
  exact
    (hR.mul_prod hiW.norm).congr
      (MeasureTheory.ae_of_all _
        (fun p ↦ by
          have he := norm_resolvent_laplace_mul a p.1 (-p.2) (W p.2)
          simpa only [Complex.ofReal_neg, mul_neg, neg_div, sub_eq_add_neg, Pi.mul_apply,
            Function.comp_apply] using he.symm))

/-- For positive decay and a continuous integrable weight, express the reflected resolvent
integral as an iterated Laplace integral. Substitute the half-line representation and use
absolute Fubini. The negative height sign matches reflected Gamma denominators. -/
theorem reflected_resolvent_integral_eq_laplace_weight {a : ℝ} (ha : 0 < a) (W : ℝ → ℂ)
    (hW : Continuous W) (hiW : MeasureTheory.Integrable W) :
    (∫ t : ℝ, (1 / ((a : ℂ) - Complex.I * (t : ℂ) / 2)) * W t) =
      ∫ r : ℝ in Set.Ioi 0,
        ∫ t : ℝ, Complex.exp (-((a : ℂ) - Complex.I * (t : ℂ) / 2) * (r : ℂ)) * W t := by
  calc
    _ =
        ∫ t : ℝ,
          ∫ r : ℝ in Set.Ioi 0,
            Complex.exp (-((a : ℂ) - Complex.I * (t : ℂ) / 2) * (r : ℂ)) * W t :=
      by
      apply MeasureTheory.integral_congr_ae
      exact
        MeasureTheory.ae_of_all _
          (fun t ↦ by
            have he := central_resolvent_eq_laplace ha (-t)
            simp only [Complex.ofReal_neg, mul_neg, neg_div, ← sub_eq_add_neg] at he
            dsimp only
            rw [he, MeasureTheory.integral_mul_const])
    _ = _ :=
      (MeasureTheory.integral_integral_swap
          (integrable_reflected_resolvent_laplace_mul_weight ha W hW hiW)).symm

/-- The adjustable rational kernel on the vertical line Re(s)=c times the Mellin power x^s.
The real parameters h,c,x,t are totalized. Later lemmas impose a line between the poles
and positive scale to obtain regularity and exact signed integral formulas. -/
noncomputable def reciprocalGapMiddleWeight (h c x t : ℝ) : ℂ :=
  Analysis.reciprocalGapFunction h ((c : ℂ) + Complex.I * t) * (x : ℂ) ^ ((c : ℂ) + Complex.I * t)

/-- For a line strictly between the two poles and positive scale, the actual Mellin weight
is continuous. Each denominator has a nonzero real part and the complex power base is
positive. This supplies regularity for the reflected Laplace and digamma exchanges. -/
theorem continuous_reciprocalGapMiddleWeight {h c x : ℝ} (hcl : -1 / 2 - h < c) (hcu : c < -1 / 2)
    (hx : 0 < x) : Continuous (reciprocalGapMiddleWeight h c x) := by
  have hL : Continuous (fun t : ℝ ↦ (c : ℂ) + Complex.I * t) :=
    continuous_const.add (continuous_const.mul Complex.continuous_ofReal)
  have hn (a : ℝ) (ha : c + a ≠ 0) (t : ℝ) : (c : ℂ) + Complex.I * t + (a : ℂ) ≠ 0 := by
    apply ne_of_apply_ne Complex.re
    simpa only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, zero_mul, mul_zero, sub_zero, add_zero, Complex.zero_re] using ha
  have hK : Continuous (fun t : ℝ ↦ Analysis.reciprocalGapFunction h ((c : ℂ) + Complex.I * t)) :=
    continuous_const.div ((hL.add_const ((1 / 2 : ℝ) : ℂ)).mul (hL.add_const ((1 / 2 + h : ℝ) : ℂ)))
      (fun t ↦
        mul_ne_zero (hn (1 / 2) (by linarith only [hcu]) t)
          (hn (1 / 2 + h) (by linarith only [hcl]) t))
  exact hK.mul (hL.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne')))

/-- For a line between the two poles and positive scale, the Mellin weight is integrable.
Reuse the general middle-line kernel estimate. This discharges the reflected Fubini premise. -/
theorem integrable_reciprocalGapMiddleWeight {h c x : ℝ} (hcl : -1 / 2 - h < c) (hcu : c < -1 / 2)
    (hx : 0 < x) : MeasureTheory.Integrable (reciprocalGapMiddleWeight h c x) := by
  exact integrable_reciprocalGap_middle_kernel hcl hcu hx

/-- For positive scale and arbitrary real parameters, a reflected Laplace phase changes
the Mellin scale to x*exp(r/2) and leaves exp(-a*r). Expand powers using real logarithms.
This exact identity retains the sign of the middle-strip inverse transform. -/
theorem reciprocalGap_reflected_laplace_shift {x : ℝ} (hx : 0 < x) (h c a r t : ℝ) :
    Complex.exp (-(((a - c / 2 : ℝ) : ℂ) - Complex.I * (t : ℂ) / 2) * (r : ℂ)) *
        reciprocalGapMiddleWeight h c x t =
      (Real.exp (-a * r) : ℂ) * reciprocalGapMiddleWeight h c (x * Real.exp (r / 2)) t := by
  have hs : 0 < x * Real.exp (r / 2) := mul_pos hx (Real.exp_pos _)
  unfold reciprocalGapMiddleWeight
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hs.ne'), ← Complex.ofReal_log hx.le, ←
    Complex.ofReal_log hs.le, Real.log_mul hx.ne' (Real.exp_ne_zero _), Real.log_exp]
  simp only [Complex.ofReal_add, Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_neg,
    Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_ofNat]
  have he :
    -(((a : ℂ) - c / 2) - Complex.I * (t : ℂ) / 2) * (r : ℂ) +
        (Real.log x : ℂ) * ((c : ℂ) + Complex.I * t) =
      -(a : ℂ) * r + ((Real.log x : ℂ) + r / 2) * ((c : ℂ) + Complex.I * t) := by
    ring
  calc
    _ =
        Analysis.reciprocalGapFunction h ((c : ℂ) + Complex.I * t) *
          (Complex.exp (-(((a : ℂ) - c / 2) - Complex.I * (t : ℂ) / 2) * r) *
            Complex.exp ((Real.log x : ℂ) * ((c : ℂ) + Complex.I * t))) :=
      by ring
    _ = _ := by
      rw [← Complex.exp_add, he, Complex.exp_add]; ring

/-- For positive gap, a line between the poles, x>=1 and r>=0, evaluate the normalized
inner reflected Laplace integral by the negative middle-strip profile at x*exp(r/2).
The shifted scale stays at least one, so the same profile branch applies throughout. -/
theorem reciprocalGap_reflected_laplace_inner {h c a x r : ℝ} (hh : 0 < h) (hcl : -1 / 2 - h < c)
    (hcu : c < -1 / 2) (hx : 1 ≤ x) (hr : 0 ≤ r) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          Complex.exp (-(((a - c / 2 : ℝ) : ℂ) - Complex.I * (t : ℂ) / 2) * (r : ℂ)) *
            reciprocalGapMiddleWeight h c x t) =
      (Real.exp (-a * r) : ℂ) * ((-(x * Real.exp (r / 2)) ^ (-1 / 2 - h) / h : ℝ) : ℂ) := by
  have hs : 1 ≤ x * Real.exp (r / 2) := by
    have he : 1 ≤ Real.exp (r / 2) := Real.one_le_exp (by linarith only [hr])
    nlinarith only [mul_le_mul_of_nonneg_left he (zero_lt_one.trans_le hx).le, hx]
  rw [MeasureTheory.integral_congr_ae
      (MeasureTheory.ae_of_all _
        (fun t ↦ reciprocalGap_reflected_laplace_shift (zero_lt_one.trans_le hx) h c a r t)),
    MeasureTheory.integral_const_mul, mul_left_comm]
  exact congrArg ((Real.exp (-a * r) : ℂ) * ·) (reciprocalGap_left_kernel_integral hh hcl hcu hs)

/-- For positive scale, rewrite the reflected scalar density as a fixed signed coefficient
times exp(-(a+(1/2+h)/2)*r). Expand the positive real power and combine exponentials.
This permits exact integration over the whole positive half-line. -/
theorem reciprocalGap_reflected_density {h a x r : ℝ} (hx : 0 < x) :
    Real.exp (-a * r) * (-(x * Real.exp (r / 2)) ^ (-1 / 2 - h) / h) =
      (-x ^ (-1 / 2 - h) / h) * Real.exp (-(a + (1 / 2 + h) / 2) * r) := by
  rw [Real.mul_rpow hx.le (Real.exp_pos _).le, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  have he : -a * r + (r / 2) * (-1 / 2 - h) = -(a + (1 / 2 + h) / 2) * r := by ring
  rw [← he, Real.exp_add]
  ring

/-- For positive gap, a line between the poles, scale at least one and positive reflected
decay a-c/2, the normalized resolvent integral is -x^(-1/2-h)/(h*(a+(1/2+h)/2)).
Apply absolute Fubini, evaluate the shifted inverse transform and integrate the real
exponential density. This is the scalar input to the reflected Gamma series. -/
theorem reciprocalGap_reflected_resolvent_integral {h c a x : ℝ} (hh : 0 < h) (hcl : -1 / 2 - h < c)
    (hcu : c < -1 / 2) (hx : 1 ≤ x) (ha : 0 < a - c / 2) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          (1 / ((a : ℂ) - ((c : ℂ) + Complex.I * t) / 2)) * reciprocalGapMiddleWeight h c x t) =
      ((-x ^ (-1 / 2 - h) / (h * (a + (1 / 2 + h) / 2)) : ℝ) : ℂ) := by
  have hx0 := zero_lt_one.trans_le hx
  have hab : 0 < a + (1 / 2 + h) / 2 := by linarith only [ha, hcl]
  have he (t : ℝ) :
    (a : ℂ) - ((c : ℂ) + Complex.I * t) / 2 = ((a - c / 2 : ℝ) : ℂ) - Complex.I * t / 2 := by
    push_cast; ring
  simp only [he]
  rw [reflected_resolvent_integral_eq_laplace_weight ha (reciprocalGapMiddleWeight h c x)
      (continuous_reciprocalGapMiddleWeight hcl hcu hx0)
      (integrable_reciprocalGapMiddleWeight hcl hcu hx0),
    ← MeasureTheory.integral_const_mul]
  have hi :
    (∫ r : ℝ in Set.Ioi 0,
        ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            Complex.exp (-(((a - c / 2 : ℝ) : ℂ) - Complex.I * (t : ℂ) / 2) * (r : ℂ)) *
              reciprocalGapMiddleWeight h c x t)) =
      ∫ r : ℝ in Set.Ioi 0,
        (((-x ^ (-1 / 2 - h) / h) * Real.exp (-(a + (1 / 2 + h) / 2) * r) : ℝ) : ℂ) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
    rw [reciprocalGap_reflected_laplace_inner hh hcl hcu hx hr.le, ← Complex.ofReal_mul,
      reciprocalGap_reflected_density hx0]
  rw [hi, integral_complex_ofReal, MeasureTheory.integral_const_mul,
    integral_exp_mul_Ioi (neg_neg_of_pos hab) 0]
  simp only [mul_zero, Real.exp_zero, neg_div_neg_eq]
  push_cast
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- For a line between the poles and positive scale, some real constant bounds the
Mellin-weight norm by A/(1+t^2). Translate the rational poles and use absolute-product
resolvent domination. The constant is needed only for convergence, not the final error. -/
theorem norm_reciprocalGapMiddleWeight_quadratic {h c x : ℝ} (hcl : -1 / 2 - h < c)
    (hcu : c < -1 / 2) (hx : 0 < x) :
    ∃ A : ℝ, ∀ t : ℝ, ‖reciprocalGapMiddleWeight h c x t‖ ≤ A / (1 + t ^ 2) := by
  let v := |(c + 1 / 2) * (c + (1 / 2 + h))|
  have hv : 0 < v := abs_pos.mpr (mul_ne_zero (by linarith only [hcu]) (by linarith only [hcl]))
  have he (t : ℝ) :
    Analysis.reciprocalGapFunction h ((c : ℂ) + Complex.I * t) =
      Analysis.twoPoleFunction (c + 1 / 2) (c + (1 / 2 + h)) (Complex.I * t) := by
    unfold Analysis.reciprocalGapFunction Analysis.twoPoleFunction
    push_cast
    congr 1
    ring
  refine ⟨x ^ c * (1 + v⁻¹), fun t ↦ ?_⟩
  have hk :=
    Analysis.twoPoleFunction_norm_le_abs_resolvent (t := t) (Real.sqrt_pos.mpr hv)
      (le_of_eq (Real.sq_sqrt hv.le))
  rw [Real.sq_sqrt hv.le] at hk
  have hc : 1 / (v + t ^ 2) ≤ (1 + v⁻¹) / (1 + t ^ 2) := by
    apply
      (div_le_div_iff₀ (add_pos_of_pos_of_nonneg hv (sq_nonneg t))
          (by nlinarith only [sq_nonneg t] : (0 : ℝ) < 1 + t ^ 2)).mpr
    have hi : v * v⁻¹ = 1 := mul_inv_cancel₀ hv.ne'
    nlinarith only [hi, hv, mul_nonneg (inv_pos.mpr hv).le (sq_nonneg t)]
  rw [reciprocalGapMiddleWeight, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
  rw [he]
  exact (mul_le_mul_of_nonneg_right (hk.trans hc) (Real.rpow_pos_of_pos hx c).le).trans_eq (by ring)

end PseudoPrime.LLS.PaperStatements
