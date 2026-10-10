/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.TriangularMellin
public import PseudoPrime.AnalyticNumberTheory.General.MellinWeights

/-! # Inversion of the triangular Mellin kernel

Scaled logarithmic weights invert the three inverse-square summands of
the exponential quotient squared on a positive vertical line.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.General

/-- Scaling a positive real argument by an exponential multiplies its
complex power by the corresponding complex exponential. The positive-real
quotient power rule and logarithm of exp prove the identity used in Mellin integrands. -/
private theorem cpow_exp_scale {u : ℝ} (hu : 0 < u) (b : ℝ) (s : ℂ) :
    (((u / Real.exp b : ℝ) : ℂ) ^ (-s)) = Complex.exp ((b : ℂ) * s) * (u : ℂ) ^ (-s) := by
  rw [cpow_div_eq_cpow_mul_cpow_neg hu.le (Real.exp_pos b), neg_neg,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos b).ne'), ←
    Complex.ofReal_log (Real.exp_pos b).le, Real.log_exp, mul_comm]

/-- For a nonzero real coordinate and a positive argument, the
inverse-square Mellin integrand is absolutely integrable. Its power factor
has constant norm along the line, so the integrable inverse-square kernel
provides a majorant. This justifies splitting the triangular integral. -/
private theorem integrable_log_inverse {c u : ℝ} (hc : c ≠ 0) (hu : 0 < u) :
    MeasureTheory.Integrable
      (fun t : ℝ ↦ (u : ℂ) ^ (-((c : ℂ) + t * Complex.I)) / ((c : ℂ) + t * Complex.I) ^ 2) := by
  have hb : MeasureTheory.Integrable (fun t : ℝ ↦ 1 / ((c : ℂ) + t * Complex.I) ^ 2) := by
    simpa only [Complex.VerticalIntegrable, one_div, inv_pow] using
      verticalIntegrable_mellinLogKernel hc
  have hm :
    MeasureTheory.AEStronglyMeasurable (fun t : ℝ ↦ (u : ℂ) ^ (-((c : ℂ) + t * Complex.I)))
      MeasureTheory.volume := by
    simp only [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hu.ne')]
    exact
      (Complex.continuous_exp.comp
          (continuous_const.mul
            ((continuous_const.add
                (Complex.continuous_ofReal.mul continuous_const)).neg))).aestronglyMeasurable
  have hh :=
    hb.bdd_mul hm (c := u ^ (-c))
      (Filter.Eventually.of_forall
        (fun t ↦ by
          rw [Complex.norm_cpow_eq_rpow_re_of_pos hu]
          simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
            Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero,
            le_refl]))
  simpa only [div_eq_mul_inv, one_mul] using hh

/-- For nonzero parameter and argument, the triangular kernel is
the sum of three exponential inverse-square terms. Expand the quotient
square and cancel the product of opposite exponentials. This supplies
the three logarithmic weights in Mellin inversion. -/
private theorem triangular_expansion {a : ℝ} (ha : a ≠ 0) {s : ℂ} (hs : s ≠ 0) :
    Analysis.triangularMellinFunction a s =
      (Complex.exp (2 * (a : ℂ) * s) + Complex.exp (-(2 * (a : ℂ) * s)) - 2) / s ^ 2 := by
  rw [Analysis.triangularMellinFunction_of_ne_zero ha hs, div_pow]
  congr 1
  have he := Complex.exp_add ((a : ℂ) * s) (-((a : ℂ) * s))
  rw [add_neg_cancel, Complex.exp_zero] at he
  have h1 : Complex.exp ((a : ℂ) * s) ^ 2 = Complex.exp (2 * (a : ℂ) * s) := by
    rw [pow_two, ← Complex.exp_add]
    congr 1
    ring
  have h2 : Complex.exp (-((a : ℂ) * s)) ^ 2 = Complex.exp (-(2 * (a : ℂ) * s)) := by
    rw [pow_two, ← Complex.exp_add]
    congr 1
    ring
  calc
    _ =
        Complex.exp ((a : ℂ) * s) ^ 2 + Complex.exp (-((a : ℂ) * s)) ^ 2 -
          2 * (Complex.exp ((a : ℂ) * s) * Complex.exp (-((a : ℂ) * s))) :=
      by ring
    _ = _ := by rw [← he, h1, h2, mul_one]

/-- Away from the zero real coordinate, a triangular inverse integrand
splits into three scaled inverse-square integrands. Expand the entire
kernel and use positive-real exponential scaling. This is shared by
absolute integrability and the positive-line inversion formula. -/
private theorem triangular_inverse_integrand_eq {a c u : ℝ} (ha : a ≠ 0) (hc : c ≠ 0) (hu : 0 < u)
    (t : ℝ) :
    (u : ℂ) ^ (-((c : ℂ) + t * Complex.I)) *
        Analysis.triangularMellinFunction a ((c : ℂ) + t * Complex.I) =
      ((u / Real.exp (2 * a) : ℝ) : ℂ) ^ (-((c : ℂ) + t * Complex.I)) /
            ((c : ℂ) + t * Complex.I) ^ 2 +
          ((u / Real.exp (-2 * a) : ℝ) : ℂ) ^ (-((c : ℂ) + t * Complex.I)) /
            ((c : ℂ) + t * Complex.I) ^ 2 -
        2 * ((u : ℂ) ^ (-((c : ℂ) + t * Complex.I)) / ((c : ℂ) + t * Complex.I) ^ 2) := by
  have hs : (c : ℂ) + t * Complex.I ≠ 0 := by
    intro hz
    have hr := congrArg Complex.re hz
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero, Complex.zero_re] at hr
    exact hc hr
  rw [triangular_expansion ha hs, cpow_exp_scale hu (2 * a), cpow_exp_scale hu (-2 * a)]
  simp only [Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_neg]
  ring_nf

/-- For nonzero parameter and nonzero real line coordinate, the triangular
inverse Mellin integrand at a positive argument is absolutely integrable.
Split it into the three logarithmic inverse-square integrands, whose
power factors have bounded norm. This supplies every nonzero allowed
line in the triangular Mellin-kernel construction. -/
theorem integrable_triangular_inverse_of_ne_zero {a c u : ℝ} (ha : a ≠ 0) (hc : c ≠ 0)
    (hu : 0 < u) :
    MeasureTheory.Integrable
      (fun t : ℝ ↦
        (u : ℂ) ^ (-((c : ℂ) + t * Complex.I)) *
          Analysis.triangularMellinFunction a ((c : ℂ) + t * Complex.I)) := by
  have h1 := integrable_log_inverse hc (div_pos hu (Real.exp_pos (2 * a)))
  have h2 := integrable_log_inverse hc (div_pos hu (Real.exp_pos (-2 * a)))
  have h0 := integrable_log_inverse hc hu
  exact
    ((h1.add h2).sub (h0.const_mul 2)).congr
      (Filter.Eventually.of_forall (fun t ↦ (triangular_inverse_integrand_eq ha hc hu t).symm))

/-- For nonzero parameter, positive line coordinate and positive
argument, the triangular inverse Mellin transform is a sum of three
scaled logarithmic weights. The exponential scaling identity identifies
the integrands, absolute integrability permits splitting, and the known
inverse-square Mellin transform computes each summand. -/
theorem mellinInv_triangular_weight_combination {a c u : ℝ} (ha : a ≠ 0) (hc : 0 < c) (hu : 0 < u) :
    mellinInv c (Analysis.triangularMellinFunction a) u =
      mellinWeightTwo (u / Real.exp (2 * a)) + mellinWeightTwo (u / Real.exp (-2 * a)) -
        2 * mellinWeightTwo u := by
  let f := fun (v t : ℝ) ↦ (v : ℂ) ^ (-((c : ℂ) + t * Complex.I)) / ((c : ℂ) + t * Complex.I) ^ 2
  have hf {v : ℝ} (hv : 0 < v) : MeasureTheory.Integrable (f v) := integrable_log_inverse hc.ne' hv
  have hp :
    (fun t : ℝ ↦
        (u : ℂ) ^ (-((c : ℂ) + t * Complex.I)) *
          Analysis.triangularMellinFunction a ((c : ℂ) + t * Complex.I)) =
      fun t ↦ f (u / Real.exp (2 * a)) t + f (u / Real.exp (-2 * a)) t - 2 * f u t := by
    funext t
    exact triangular_inverse_integrand_eq ha hc.ne' hu t
  have h1 := mellinInv_mellinWeightTwo_eq hc (div_pos hu (Real.exp_pos (2 * a)))
  have h2 := mellinInv_mellinWeightTwo_eq hc (div_pos hu (Real.exp_pos (-2 * a)))
  have h0 := mellinInv_mellinWeightTwo_eq hc hu
  rw [← h1, ← h2, ← h0]
  simp only [mellinInv, smul_eq_mul]
  rw [hp]
  have hadd :=
    MeasureTheory.integral_add (hf (div_pos hu (Real.exp_pos (2 * a))))
      (hf (div_pos hu (Real.exp_pos (-2 * a))))
  change
    (∫ t : ℝ, f (u / Real.exp (2 * a)) t + f (u / Real.exp (-2 * a)) t) =
      (∫ t : ℝ, f (u / Real.exp (2 * a)) t) + (∫ t : ℝ, f (u / Real.exp (-2 * a)) t) at hadd
  have hsub :=
    MeasureTheory.integral_sub
      ((hf (div_pos hu (Real.exp_pos (2 * a)))).add (hf (div_pos hu (Real.exp_pos (-2 * a)))))
      ((hf hu).const_mul 2)
  change
    (∫ t : ℝ, (f (u / Real.exp (2 * a)) t + f (u / Real.exp (-2 * a)) t) - 2 * f u t) =
      (∫ t : ℝ, f (u / Real.exp (2 * a)) t + f (u / Real.exp (-2 * a)) t) -
        (∫ t : ℝ, 2 * f u t) at hsub
  rw [hsub, hadd, MeasureTheory.integral_const_mul]
  dsimp only [f]
  simp only [div_eq_mul_inv, one_mul, smul_sub, smul_add, Complex.real_smul, Complex.ofReal_mul]
  ring

/-- At a positive argument the logarithmic smoothing weight is the
positive part of minus its logarithm. Split at one and use the sign of
the logarithm. This expresses the triangular inverse transform using maxima. -/
private theorem mellinWeightTwo_eq_max {u : ℝ} (hu : 0 < u) :
    mellinWeightTwo u = ((max 0 (-Real.log u) : ℝ) : ℂ) := by
  by_cases hle : u ≤ 1
  · have hm : u ∈ Set.Ioc (0 : ℝ) 1 := ⟨hu, hle⟩
    have hn : 0 ≤ -Real.log u := neg_nonneg.mpr (Real.log_nonpos hu.le hle)
    rw [mellinWeightTwo, Set.indicator_of_mem hm, max_eq_right hn, Complex.ofReal_neg]
  · have hgt : 1 < u := lt_of_not_ge hle
    have hm : u ∉ Set.Ioc (0 : ℝ) 1 := fun he ↦ hle he.2
    have hn : -Real.log u ≤ 0 := neg_nonpos.mpr (Real.log_pos hgt).le
    rw [mellinWeightTwo, Set.indicator_of_notMem hm, max_eq_left hn, Complex.ofReal_zero]

/-- For a nonnegative width, three positive-part linear functions
combine to the triangular profile. Split by the sign of the argument
and the support boundary. This identifies the logarithmic weight combination. -/
private theorem triangular_max_combination {a L : ℝ} (ha : 0 ≤ a) :
    max 0 (2 * a - L) + max 0 (-2 * a - L) - 2 * max 0 (-L) = max 0 (2 * a - |L|) := by
  by_cases hL : 0 ≤ L
  · rw [abs_of_nonneg hL, max_eq_left (by linarith only [ha, hL] : -2 * a - L ≤ 0),
      max_eq_left (neg_nonpos.mpr hL)]
    ring
  · have hLn : L ≤ 0 := (lt_of_not_ge hL).le
    rw [abs_of_nonpos hLn, max_eq_right (by linarith only [ha, hLn] : 0 ≤ 2 * a - L),
      max_eq_right (neg_nonneg.mpr hLn)]
    rw [sub_neg_eq_add]
    by_cases hb : 0 ≤ 2 * a + L
    · rw [max_eq_left (by linarith only [hb] : -2 * a - L ≤ 0), max_eq_right hb]
      ring
    · rw [max_eq_right (by linarith only [hb] : 0 ≤ -2 * a - L), max_eq_left (lt_of_not_ge hb).le]
      ring

/-- For positive parameter, positive line coordinate and positive
argument, the inverse Mellin transform of the entire triangular kernel
is `max(0, 2*a-abs(log u))`. Compute the three logarithmic weights and
simplify their positive parts. This is the Section 6.2 transform identity
on a positive line, without any numerical integration assumption. -/
theorem mellinInv_triangular_of_pos {a c u : ℝ} (ha : 0 < a) (hc : 0 < c) (hu : 0 < u) :
    mellinInv c (Analysis.triangularMellinFunction a) u =
      ((max 0 (2 * a - |Real.log u|) : ℝ) : ℂ) := by
  rw [mellinInv_triangular_weight_combination ha.ne' hc hu,
    mellinWeightTwo_eq_max (div_pos hu (Real.exp_pos (2 * a))),
    mellinWeightTwo_eq_max (div_pos hu (Real.exp_pos (-2 * a))), mellinWeightTwo_eq_max hu]
  have hl (b : ℝ) : -Real.log (u / Real.exp b) = b - Real.log u := by
    rw [Real.log_div hu.ne' (Real.exp_pos b).ne', Real.log_exp]
    ring
  rw [hl (2 * a), hl (-2 * a)]
  have hcast : (2 : ℂ) = ((2 : ℝ) : ℂ) := rfl
  rw [hcast, ← Complex.ofReal_mul, ← Complex.ofReal_add, ← Complex.ofReal_sub]
  exact congrArg Complex.ofReal (triangular_max_combination ha.le)

/-- The sine square is at most one. Square its absolute-value
bound to obtain the integrable-tail estimate for the triangular kernel. -/
private theorem sin_sq_le_one (x : ℝ) : Real.sin x ^ 2 ≤ 1 := by
  have h := mul_self_le_mul_self (abs_nonneg (Real.sin x)) (Real.abs_sin_le_one x)
  simpa only [← pow_two, sq_abs, one_pow] using h

/-- The sinc square is at most one. Square its absolute-value
bound to control the triangular kernel at small imaginary heights. -/
private theorem sinc_sq_le_one (x : ℝ) : Real.sinc x ^ 2 ≤ 1 := by
  have h := mul_self_le_mul_self (abs_nonneg (Real.sinc x)) (Real.abs_sinc_le_one x)
  simpa only [← pow_two, sq_abs, one_pow] using h

/-- For a nonzero parameter, the imaginary-axis norm of the
triangular kernel is bounded by `8*(a²+1)/(1+t²)`. At small heights use
the bounded sinc function, and at large heights cancel the parameter
and bound sine. This controls the inverse integral across the removable origin. -/
private theorem triangular_imaginary_bound {a : ℝ} (ha : a ≠ 0) (t : ℝ) :
    ‖Analysis.triangularMellinFunction a (Complex.I * t)‖ ≤ 8 * (a ^ 2 + 1) / (1 + t ^ 2) := by
  let N := ‖Analysis.triangularMellinFunction a (Complex.I * t)‖
  have hN : 0 ≤ N := norm_nonneg _
  have hb : N ≤ 4 * a ^ 2 := by
    dsimp only [N]
    rw [Analysis.norm_triangularMellinFunction_imaginary ha]
    have h :=
      mul_le_mul_of_nonneg_left (sinc_sq_le_one (a * t))
        (show 0 ≤ 4 * a ^ 2 by exact mul_nonneg (by norm_num only) (sq_nonneg a))
    nlinarith only [h]
  apply (le_div_iff₀ (by nlinarith only [sq_nonneg t] : 0 < 1 + t ^ 2)).mpr
  by_cases ht : t ^ 2 ≤ 1
  · nlinarith only [hN, hb, ht, sq_nonneg a]
  · have ht1 : 1 ≤ t ^ 2 := (lt_of_not_ge ht).le
    have htn : t ≠ 0 := by
      intro hz; rw [hz] at ht; norm_num only at ht
    have he : (2 * a * Real.sinc (a * t)) * t = 2 * Real.sin (a * t) := by
      rw [Real.sinc_of_ne_zero (mul_ne_zero ha htn)]
      calc
        _ = (Real.sin (a * t) / (a * t)) * (a * t) * 2 := by ring
        _ = _ := by
          rw [div_mul_cancel₀ _ (mul_ne_zero ha htn)]; ring
    have hp : N * t ^ 2 ≤ 4 := by
      dsimp only [N]
      rw [Analysis.norm_triangularMellinFunction_imaginary ha, ← mul_pow, he]
      have hs := sin_sq_le_one (a * t)
      nlinarith only [hs]
    have hn := mul_le_mul_of_nonneg_left ht1 hN
    nlinarith only [hp, hn, sq_nonneg a]

/-- The triangular kernel is absolutely integrable on the
imaginary axis for a nonzero parameter. Its continuous entire extension
and a quadratic norm majorant prove integrability, including the origin. -/
private theorem integrable_triangular_imaginary {a : ℝ} (ha : a ≠ 0) :
    MeasureTheory.Integrable (fun t : ℝ ↦ Analysis.triangularMellinFunction a (Complex.I * t)) := by
  have hm : Continuous (fun t : ℝ ↦ Analysis.triangularMellinFunction a (Complex.I * t)) :=
    (Analysis.differentiable_triangularMellinFunction a).continuous.comp
      (continuous_const.mul Complex.continuous_ofReal)
  apply (integrable_inv_one_add_sq.const_mul (8 * (a ^ 2 + 1))).mono' hm.aestronglyMeasurable
  exact
    Filter.Eventually.of_forall
      (fun t ↦ by simpa only [div_eq_mul_inv] using triangular_imaginary_bound ha t)

/-- For a nonzero parameter and a positive argument, the
triangular inverse-Mellin integrand is absolutely integrable on every real
vertical line. Away from the imaginary axis use the three scaled logarithmic
integrands. On the axis use the sinc majorant and the unit-norm power factor.
This supplies the integrability field of the triangular Mellin kernel. -/
theorem integrable_inverseMellin_triangular {a c u : ℝ} (ha : a ≠ 0) (hu : 0 < u) :
    MeasureTheory.Integrable
      (fun t : ℝ ↦
        Analysis.triangularMellinFunction a ((c : ℂ) + Complex.I * t) *
          (u : ℂ) ^ (-((c : ℂ) + Complex.I * t))) := by
  by_cases hc : c = 0
  · subst c
    simp only [Complex.ofReal_zero, zero_add]
    have hm : Continuous (fun t : ℝ ↦ (u : ℂ) ^ (-(Complex.I * t))) :=
      (continuous_const.mul Complex.continuous_ofReal).neg.const_cpow
        (Or.inl (Complex.ofReal_ne_zero.mpr hu.ne'))
    apply (integrable_triangular_imaginary ha).mul_bdd (c := 1) hm.aestronglyMeasurable
    exact
      Filter.Eventually.of_forall
        (fun t ↦ by
          rw [Complex.norm_cpow_eq_rpow_re_of_pos hu]
          simp only [Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
            Complex.ofReal_im, zero_mul, mul_zero, sub_zero, neg_zero, Real.rpow_zero, le_refl])
  · simpa only [mul_comm] using integrable_triangular_inverse_of_ne_zero ha hc hu

end PseudoPrime.AnalyticNumberTheory.General
