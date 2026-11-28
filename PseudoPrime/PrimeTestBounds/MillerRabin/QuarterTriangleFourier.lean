/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterTriangleCosine
public import Mathlib.Analysis.Fourier.Inversion

/-! # Fourier inversion for the wide triangle Cauchy moment -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- At angular frequency w the bilateral decaying exponential is integrable
and its transform is the Cauchy density with numerator twice the decay. -/
theorem triangle_exp_transform {c : ℝ} (hc : 0 < c) (w : ℝ) :
    let f := fun t : ℝ => Complex.exp (-(c : ℂ) * (|t| : ℝ) - Complex.I * w * t)
    MeasureTheory.Integrable f ∧ (∫ t : ℝ, f t) = 2 * c / ((c : ℂ) ^ 2 + w ^ 2) := by
  intro f
  let A : ℂ := c - Complex.I * w
  let B : ℂ := -c - Complex.I * w
  have ha : 0 < A.re := by
    simpa only [A, Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero] using hc
  have hb : B.re < 0 := by
    simpa only [B, Complex.sub_re, Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero] using neg_lt_zero.mpr hc
  have hL : Set.EqOn f (fun t : ℝ => Complex.exp (A * t)) (Set.Iic 0) := by
    intro t ht
    unfold f A
    rw [abs_of_nonpos ht, Complex.ofReal_neg]
    congr 1
    ring
  have hR : Set.EqOn f (fun t : ℝ => Complex.exp (B * t)) (Set.Ioi 0) := by
    intro t ht
    unfold f B
    rw [abs_of_pos ht]
    congr 1
    ring
  have hl := (integrableOn_exp_mul_complex_Iic ha 0).congr_fun hL.symm measurableSet_Iic
  have hr := (integrableOn_exp_mul_complex_Ioi hb 0).congr_fun hR.symm measurableSet_Ioi
  have hi := hl.union hr
  rw [Set.Iic_union_Ioi, MeasureTheory.integrableOn_univ] at hi
  refine ⟨hi, ?_⟩
  rw [← MeasureTheory.integral_add_compl (s := Set.Iic 0) measurableSet_Iic hi, Set.compl_Iic,
    MeasureTheory.setIntegral_congr_fun measurableSet_Iic hL,
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hR, integral_exp_mul_complex_Iic ha,
    integral_exp_mul_complex_Ioi hb]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  have hA : A ≠ 0 := fun h => ha.ne' (by rw [h, Complex.zero_re])
  have hB : B ≠ 0 := fun h => hb.ne (by rw [h, Complex.zero_re])
  have hD : (c : ℂ) ^ 2 + w ^ 2 ≠ 0 := by
    exact_mod_cast (add_pos_of_pos_of_nonneg (sq_pos_of_pos hc) (sq_nonneg w)).ne'
  field_simp [hA, hB, hD]
  unfold A B
  linear_combination (-2 * (c : ℂ) * w ^ 2) * Complex.I_sq

/-- With decay 2πc the Fourier transform in mathlib's normalization has
denominator c²+w² and constant numerator c/π. -/
theorem triangle_fourier_exp {c : ℝ} (hc : 0 < c) (w : ℝ) :
    FourierTransform.fourier (fun t : ℝ => ((Real.exp (-(2 * Real.pi * c) * |t|) : ℝ) : ℂ)) w =
      ((c / Real.pi / (c ^ 2 + w ^ 2) : ℝ) : ℂ) := by
  rw [Real.fourier_eq']
  have he := (triangle_exp_transform (c := 2 * Real.pi * c) (by positivity) (2 * Real.pi * w)).2
  apply Eq.trans _ (he.trans _)
  · apply MeasureTheory.integral_congr_ae
    apply Filter.Eventually.of_forall
    intro t
    dsimp only
    rw [smul_eq_mul, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    rw [Real.inner_apply]
    push_cast
    ring
  · push_cast
    field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]

/-- Fourier inversion of the bilateral exponential gives the cosine transform
of the Cauchy density at every real angular frequency. -/
theorem triangle_cauchy_cosine {c : ℝ} (hc : 0 < c) (a : ℝ) :
    (∫ t : ℝ, Real.cos (a * t) / (c ^ 2 + t ^ 2)) = Real.pi / c * Real.exp (-c * |a|) := by
  let f (t : ℝ) : ℂ := Real.exp (-(2 * Real.pi * c) * |t|)
  let d (t : ℝ) := (c ^ 2 + t ^ 2)⁻¹
  have hf : MeasureTheory.Integrable f := by
    simpa only [f, Complex.ofReal_zero, mul_zero, zero_mul, sub_zero, Complex.ofReal_exp,
      Complex.ofReal_mul, Complex.ofReal_neg] using
      (triangle_exp_transform (c := 2 * Real.pi * c) (by positivity) 0).1
  have hd := Analysis.integrable_cauchy_of_pos hc
  have hg : MeasureTheory.Integrable (FourierTransform.fourier f) := by
    have h := (hd.const_mul (c / Real.pi)).ofReal (𝕜 := ℂ)
    apply h.congr (Filter.Eventually.of_forall (fun t => ?_))
    rw [triangle_fourier_exp hc]
    rfl
  let y := a / (2 * Real.pi)
  have he :=
    congrFun
      ((show Continuous f by
            unfold f; fun_prop).fourierInv_fourier_eq
        hf hg)
      y
  rw [Real.fourierInv_eq'] at he
  let g (t : ℝ) := Complex.exp (((a * t : ℝ) : ℂ) * Complex.I) * ((c / Real.pi * d t : ℝ) : ℂ)
  have hpoint (t : ℝ) :
    Complex.exp (((2 * Real.pi * inner ℝ t y : ℝ) : ℂ) * Complex.I) • FourierTransform.fourier f t =
      g t := by
    rw [triangle_fourier_exp hc, Real.inner_apply, smul_eq_mul]
    have hy : 2 * Real.pi * (t * y) = a * t := by
      unfold y; field_simp
    rw [hy]
    rfl
  simp_rw [hpoint] at he
  have hgi : MeasureTheory.Integrable g := by
    apply
      ((hd.const_mul (c / Real.pi))).mono'
        (by
          unfold g d; fun_prop)
    apply Filter.Eventually.of_forall
    intro t
    unfold g d
    rw [norm_mul, Complex.norm_exp, Complex.mul_I_re, Complex.ofReal_im, neg_zero, Real.exp_zero,
      one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hreal := congrArg Complex.re he
  have hreal' : (∫ t : ℝ, (g t).re) = (f y).re := (integral_re hgi).trans hreal
  have hr (t : ℝ) : (g t).re = (c / Real.pi) * (Real.cos (a * t) / (c ^ 2 + t ^ 2)) := by
    unfold g d
    rw [Complex.mul_re, Complex.ofReal_im, mul_zero, sub_zero, Complex.ofReal_re,
      Complex.exp_ofReal_mul_I_re]
    ring
  simp_rw [hr] at hreal'
  rw [MeasureTheory.integral_const_mul] at hreal'
  have hy : -(2 * Real.pi * c) * |y| = -c * |a| := by
    rw [show |y| = |a| / (2 * Real.pi) by
        unfold y
        rw [abs_div, abs_of_pos (show 0 < 2 * Real.pi by positivity)]]
    field_simp
  change _ = Real.exp (-(2 * Real.pi * c) * |y|) at hreal'
  rw [hy] at hreal'
  rw [← hreal']
  field_simp

/-- The exact integrated digamma pole at positive width and positive shift
retains its exponential factor, as required by the origin correction series. -/
theorem triangle_digamma_pole_exact {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    (∫ t : ℝ,
        (1 / 2 : ℝ) * ((t / 2) ^ 2 / (r * (r ^ 2 + (t / 2) ^ 2))) *
          ‖Analysis.triangularMellinFunction a (Complex.I * t)‖) =
      Real.pi / (2 * r ^ 2) * (1 - Real.exp (-(4 * a * r))) := by
  rw [triangle_digamma_pole ha.ne' hr, triangle_cauchy_cosine (by positivity),
    abs_of_pos (show 0 < 2 * a by positivity)]
  rw [show -(2 * r) * (2 * a) = -(4 * a * r) by ring]
  field_simp

end PseudoPrime.PrimeTestBounds.MillerRabin
