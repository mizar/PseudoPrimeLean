/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianPrincipalHeadLog
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Ring

/-! # Height derivatives of the principal head and middle terms -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The head integrand with its phase combined into one exponential. -/
@[expose]
public noncomputable def principalHeadIntegrand (B : Polynomial ℝ) (a b t v : ℝ) : ℂ :=
  Complex.exp ((-(a * v) : ℝ) + (((b - v) * t : ℝ) : ℂ) * Complex.I) * Complex.ofReal (B.eval v)

/-- Differentiating in the height inserts the factor `i(b-v)`. -/
private theorem head_integrand_deriv (B : Polynomial ℝ) (a b t v : ℝ) :
    HasDerivAt (fun x ↦ principalHeadIntegrand B a b x v)
      (((b - v : ℝ) : ℂ) * Complex.I * principalHeadIntegrand B a b t v) t := by
  have h := ((hasDerivAt_id t).const_mul (b - v))
  have hc := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t h
  have he := ((hc.mul_const Complex.I).const_add ((-(a * v) : ℝ) : ℂ)).cexp
  have hh := he.mul_const (Complex.ofReal (B.eval v))
  simp only [Function.comp_apply, id_eq, Complex.ofRealCLM_apply, mul_one] at hh
  exact
    hh.congr_deriv
      (by
        unfold principalHeadIntegrand; ring)

/-- The derivative has a height-independent integrable absolute majorant. -/
private theorem head_deriv_norm (B : Polynomial ℝ) (a b t v : ℝ) :
    ‖((b - v : ℝ) : ℂ) * Complex.I * principalHeadIntegrand B a b t v‖ =
      |b - v| * (Real.exp (-(a * v)) * |B.eval v|) := by
  simp only [principalHeadIntegrand, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
    Complex.norm_exp, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im, mul_zero, sub_zero, add_zero, Real.norm_eq_abs]

/-- The head's height derivative is the interval integral of the differentiated integrand. -/
public theorem principal_head_height_deriv (B : Polynomial ℝ) (a b t : ℝ) :
    HasDerivAt (fun x ↦ ∫ v in (0 : ℝ)..b, principalHeadIntegrand B a b x v)
      (∫ v in (0 : ℝ)..b, ((b - v : ℝ) : ℂ) * Complex.I * principalHeadIntegrand B a b t v) t := by
  have hc (x : ℝ) : Continuous (principalHeadIntegrand B a b x) := by
    unfold principalHeadIntegrand
    fun_prop
  have hd : Continuous (fun v ↦ ((b - v : ℝ) : ℂ) * Complex.I * principalHeadIntegrand B a b t v) :=
    ((Complex.continuous_ofReal.comp (continuous_const.sub continuous_id)).mul continuous_const).mul
      (hc t)
  have hn : Continuous (fun v ↦ |b - v| * (Real.exp (-(a * v)) * |B.eval v|)) := by fun_prop
  exact
    (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le Filter.univ_mem
        (Filter.Eventually.of_forall (fun x ↦ (hc x).aestronglyMeasurable))
        ((hc t).intervalIntegrable _ _) hd.aestronglyMeasurable
        (Filter.Eventually.of_forall (fun v _ x _ ↦ (head_deriv_norm B a b x v).le))
        (hn.intervalIntegrable _ _)
        (Filter.Eventually.of_forall (fun v _ x _ ↦ head_integrand_deriv B a b x v))).2

/-- Combining the exponentials recovers the head term in H25 on the critical line. -/
public theorem principal_head_integral_eq (B : Polynomial ℝ) (a b t : ℝ) :
    (∫ v in (0 : ℝ)..b, principalHeadIntegrand B a b t v) =
      Complex.exp ((b : ℂ) * Complex.I * t) *
        ∫ v in (0 : ℝ)..b,
          Complex.exp (-(v : ℂ) * ((a : ℂ) + Complex.I * t)) * Complex.ofReal (B.eval v) := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro v _
  dsimp only [principalHeadIntegrand]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  simp only [Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_sub]
  ring

/-- A twice differentiable amplitude vanishing at both endpoints has a Fourier
moment bounded by its endpoint derivatives and the integral of its second derivative. -/
public theorem principal_fourier_second_bound {f f₁ f₂ : ℝ → ℂ} {b t : ℝ} (hb : 0 ≤ b) (ht : t ≠ 0)
    (hc : Continuous f) (hc₁ : Continuous f₁) (hc₂ : Continuous f₂)
    (hd : ∀ v, HasDerivAt f (f₁ v) v) (hd₁ : ∀ v, HasDerivAt f₁ (f₂ v) v) (h₀ : f 0 = 0)
    (h₁ : f b = 0) :
    ‖∫ v in (0 : ℝ)..b, f v * Complex.exp (-(v : ℂ) * Complex.I * t)‖ ≤
      (‖f₁ b‖ + ‖f₁ 0‖ + ∫ v in (0 : ℝ)..b, ‖f₂ v‖) / t ^ 2 := by
  let c := -Complex.I * (t : ℂ)
  let p := fun v : ℝ ↦ Complex.exp (c * (v : ℂ))
  have hp : Continuous p := by
    unfold p; fun_prop
  have hpd (v : ℝ) : HasDerivAt p (c * p v) v := by
    have h := (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt v (hasDerivAt_id v)).const_mul c
    simpa only [p, Function.comp_apply, id_eq, Complex.ofRealCLM_apply, Complex.ofReal_one, mul_one,
      mul_comm] using h.cexp
  have hi : IntervalIntegrable (fun v ↦ c * p v) MeasureTheory.volume 0 b :=
    (hp.const_mul c).intervalIntegrable _ _
  have hA :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt hc.continuousOn hp.continuousOn
      (fun v _ ↦ hd v) (fun v _ ↦ hpd v) (hc₁.intervalIntegrable _ _) hi
  have hB :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt hc₁.continuousOn hp.continuousOn
      (fun v _ ↦ hd₁ v) (fun v _ ↦ hpd v) (hc₂.intervalIntegrable _ _) hi
  have pull (g : ℝ → ℂ) :
    (∫ v in (0 : ℝ)..b, g v * (c * p v)) = c * ∫ v in (0 : ℝ)..b, g v * p v := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr (fun v _ ↦ mul_left_comm _ _ _)
  rw [pull f, h₀, h₁, zero_mul, zero_mul, sub_self, zero_sub] at hA
  rw [pull f₁] at hB
  have h := congrArg (c * ·) hA
  rw [mul_neg, hB, ← mul_assoc, ← pow_two] at h
  have hphase (v : ℝ) : ‖p v‖ = 1 := by
    unfold p c
    simp only [Complex.norm_exp, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul,
      sub_zero, neg_zero, Real.exp_zero]
  have hn : ‖c‖ = |t| := by
    simp only [c, norm_mul, norm_neg, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, one_mul]
  have hI :=
    intervalIntegral.norm_integral_le_integral_norm (a := 0) (b := b) (μ := MeasureTheory.volume)
      (f := fun v ↦ f₂ v * p v)
  have hI' : ‖∫ v in (0 : ℝ)..b, f₂ v * p v‖ ≤ ∫ v in (0 : ℝ)..b, ‖f₂ v‖ := by
    refine (hI hb).trans_eq (intervalIntegral.integral_congr (fun v _ ↦ ?_))
    rw [norm_mul, hphase, mul_one]
  have hb' :
    ‖-(f₁ b * p b - f₁ 0 * p 0 - ∫ v in (0 : ℝ)..b, f₂ v * p v)‖ ≤
      ‖f₁ b‖ + ‖f₁ 0‖ + ∫ v in (0 : ℝ)..b, ‖f₂ v‖ := by
    rw [norm_neg]
    refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans_eq ?_) hI')
    rw [norm_mul, norm_mul, hphase, hphase, mul_one, mul_one]
  rw [← h, norm_mul, norm_pow, hn, sq_abs] at hb'
  apply (le_div_iff₀ (sq_pos_of_ne_zero ht)).mpr
  rw [mul_comm]
  convert hb' using 3
  apply intervalIntegral.integral_congr
  intro v _
  dsimp only [p, c]
  congr 2
  ring

/-- The real exponential weight shifts the derivative polynomial by the rate. -/
private theorem weighted_poly_deriv (P : Polynomial ℝ) (a v : ℝ) :
    HasDerivAt (fun x : ℝ ↦ Complex.ofReal (Real.exp (-a * x) * P.eval x))
      (Complex.ofReal (Real.exp (-a * v) * (P.derivative - Polynomial.C a * P).eval v)) v := by
  have he := ((hasDerivAt_id v).const_mul (-a)).exp.mul (P.hasDerivAt v)
  have hc := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt v he
  refine hc.congr_deriv ?_
  simp only [id_eq, mul_one, Complex.ofRealCLM_apply, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_C]
  congr 1
  ring

/-- The head's derivative contribution in H26 decays quadratically with height.
The endpoint at zero vanishes with the profile and its first derivative. -/
public theorem principal_head_deriv_bound (B : Polynomial ℝ) (a b t : ℝ) (hb : 0 ≤ b) (ht : t ≠ 0)
    (hB : B.eval 0 = 0) (hB' : B.derivative.eval 0 = 0) :
    let A := (Polynomial.C b - Polynomial.X) * B
    let D :=
      A.derivative.derivative - Polynomial.C (2 * a) * A.derivative + Polynomial.C (a ^ 2) * A
    ‖deriv (fun x ↦ ∫ v in (0 : ℝ)..b, principalHeadIntegrand B a b x v) t‖ ≤
      (Real.exp (-a * b) * |B.eval b| + ∫ v in (0 : ℝ)..b, Real.exp (-a * v) * |D.eval v|) /
        t ^ 2 := by
  intro A D
  let A₁ := A.derivative - Polynomial.C a * A
  let A₂ := A₁.derivative - Polynomial.C a * A₁
  let w := fun (P : Polynomial ℝ) (v : ℝ) ↦ Complex.ofReal (Real.exp (-a * v) * P.eval v)
  have hc (P : Polynomial ℝ) : Continuous (w P) := by
    unfold w
    fun_prop
  have hA₀ : A.eval 0 = 0 := by
    simp only [A, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X,
      hB, mul_zero]
  have hAb : A.eval b = 0 := by
    simp only [A, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X,
      sub_self, zero_mul]
  have hAd (v : ℝ) : A.derivative.eval v = -B.eval v + (b - v) * B.derivative.eval v := by
    simp only [A, Polynomial.derivative_mul, Polynomial.derivative_sub, Polynomial.derivative_C,
      Polynomial.derivative_X, zero_sub, Polynomial.eval_add, Polynomial.eval_neg,
      Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, neg_mul,
      one_mul]
  have h₀ : w A₁ 0 = 0 := by
    simp only [w, A₁, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, hAd, hA₀, hB,
      hB', neg_zero, mul_zero, add_zero, sub_zero, Complex.ofReal_zero]
  have hb' : ‖w A₁ b‖ = Real.exp (-a * b) * |B.eval b| := by
    simp only [w, A₁, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, hAd, hAb,
      sub_self, zero_mul, add_zero, mul_zero, sub_zero, Complex.norm_real, Real.norm_eq_abs,
      abs_mul, abs_neg, abs_of_pos (Real.exp_pos _)]
  have hD : A₂ = D := by
    simp only [A₂, A₁, D, Polynomial.derivative_sub, Polynomial.derivative_C_mul, Polynomial.C_mul,
      Polynomial.C_pow, Polynomial.C_ofNat]
    ring
  have h :=
    principal_fourier_second_bound (f := w A) (f₁ := w A₁) (f₂ := w A₂) hb ht (hc A) (hc A₁) (hc A₂)
      (weighted_poly_deriv A a) (weighted_poly_deriv A₁ a)
      (by simp only [w, hA₀, mul_zero, Complex.ofReal_zero])
      (by simp only [w, hAb, mul_zero, Complex.ofReal_zero])
  rw [h₀, norm_zero, hb', add_zero, hD] at h
  have hnorm (v : ℝ) : ‖w D v‖ = Real.exp (-a * v) * |D.eval v| := by
    simp only [w, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  simp only [hnorm] at h
  have hphase : ‖Complex.I * Complex.exp ((b : ℂ) * Complex.I * t)‖ = 1 := by
    simp only [norm_mul, Complex.norm_I, Complex.norm_exp, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul,
      sub_self, Real.exp_zero, one_mul]
  have he :
    (∫ v in (0 : ℝ)..b, ((b - v : ℝ) : ℂ) * Complex.I * principalHeadIntegrand B a b t v) =
      (Complex.I * Complex.exp ((b : ℂ) * Complex.I * t)) *
        ∫ v in (0 : ℝ)..b, w A v * Complex.exp (-(v : ℂ) * Complex.I * t) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro v _
    simp only [principalHeadIntegrand, A, w, Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C, Complex.ofReal_mul, Complex.ofReal_exp,
      Complex.ofReal_sub, Complex.ofReal_neg]
    have hex :
      Complex.exp (-((a : ℂ) * v) + ((b : ℂ) - v) * t * Complex.I) =
        Complex.exp ((b : ℂ) * Complex.I * t) * Complex.exp (-(a : ℂ) * v) *
          Complex.exp (-(v : ℂ) * Complex.I * t) := by
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      ring
    rw [hex]
    ring
  rw [(principal_head_height_deriv B a b t).deriv, he, norm_mul, hphase, one_mul]
  exact h

/-- Expanding the weighted second derivative gives the polynomial `Z_B` from H26. -/
public theorem head_second_poly_eq (B : Polynomial ℝ) (a b : ℝ) :
    let A := (Polynomial.C b - Polynomial.X) * B
    A.derivative.derivative - Polynomial.C (2 * a) * A.derivative + Polynomial.C (a ^ 2) * A =
      (Polynomial.C b - Polynomial.X) *
            (B.derivative.derivative - Polynomial.C (2 * a) * B.derivative +
              Polynomial.C (a ^ 2) * B) -
          2 * B.derivative +
        Polynomial.C (2 * a) * B := by
  intro A
  simp only [A, Polynomial.derivative_mul, Polynomial.derivative_add, Polynomial.derivative_sub,
    Polynomial.derivative_C, Polynomial.derivative_X, Polynomial.derivative_neg,
    Polynomial.derivative_one, Polynomial.C_mul, Polynomial.C_ofNat, zero_sub]
  ring

/-- For either high Gaussian kernel, the head in H25 satisfies its term of H26. -/
public theorem high_principal_head_deriv_bound (K : HighGaussianKernel) {t : ℝ} (ht : t ≠ 0) :
    let B := K.realProfile
    let a := (K.pole : ℝ)
    let D :=
      (Polynomial.C 5 - Polynomial.X) *
            (B.derivative.derivative - Polynomial.C (2 * a) * B.derivative +
              Polynomial.C (a ^ 2) * B) -
          2 * B.derivative +
        Polynomial.C (2 * a) * B
    ‖deriv
          (fun x : ℝ ↦
            Complex.exp (5 * Complex.I * x) *
              ∫ v in (0 : ℝ)..5,
                Complex.exp (-(v : ℂ) * ((a : ℂ) + Complex.I * x)) * Complex.ofReal (B.eval v))
          t‖ ≤
      (Real.exp (-a * 5) * |B.eval 5| + ∫ v in (0 : ℝ)..5, Real.exp (-a * v) * |D.eval v|) /
        t ^ 2 := by
  intro B a D
  have h :=
    principal_head_deriv_bound B a 5 t (by norm_num only) ht (high_real_profile_at_zero K).1
      (high_real_profile_at_zero K).2
  dsimp only at h
  rw [head_second_poly_eq B a 5] at h
  rw [show
      (fun x : ℝ ↦
          Complex.exp (5 * Complex.I * x) *
            ∫ v in (0 : ℝ)..5,
              Complex.exp (-(v : ℂ) * ((a : ℂ) + Complex.I * x)) * Complex.ofReal (B.eval v)) =
        (fun x ↦ ∫ v in (0 : ℝ)..5, principalHeadIntegrand B a 5 x v)
      by
      funext x
      simpa only [Complex.ofReal_ofNat] using (principal_head_integral_eq B a 5 x).symm]
  exact h

/-- The finite head term in H25 on the critical line, as a function of height. -/
@[expose]
public noncomputable def highPrincipalHead (K : HighGaussianKernel) (t : ℝ) : ℂ :=
  let a := (K.pole : ℝ)
  Complex.exp (5 * Complex.I * t) *
    ∫ v in (0 : ℝ)..5,
      Complex.exp (-(v : ℂ) * ((a : ℂ) + Complex.I * t)) * Complex.ofReal (K.realProfile.eval v)

/-- The coefficient multiplying the inverse square in the head derivative bound. -/
@[expose]
public noncomputable def highPrincipalHeadCap (K : HighGaussianKernel) : ℝ :=
  let a := (K.pole : ℝ)
  let B := K.realProfile
  let D :=
    (Polynomial.C 5 - Polynomial.X) *
          (B.derivative.derivative - Polynomial.C (2 * a) * B.derivative +
            Polynomial.C (a ^ 2) * B) -
        2 * B.derivative +
      Polynomial.C (2 * a) * B
  Real.exp (-a * 5) * |B.eval 5| + ∫ v in (0 : ℝ)..5, Real.exp (-a * v) * |D.eval v|

/-- The height-independent multiplier in the head derivative bound is nonnegative. -/
public theorem high_principal_head_cap_nonneg (K : HighGaussianKernel) :
    0 ≤ highPrincipalHeadCap K := by
  unfold highPrincipalHeadCap
  exact
    add_nonneg (mul_nonneg (Real.exp_pos _).le (abs_nonneg _))
      (intervalIntegral.integral_nonneg (by norm_num only)
        (fun _ _ ↦ mul_nonneg (Real.exp_pos _).le (abs_nonneg _)))

/-- The head varies by at most its H26 derivative bound times the distance between
two heights in a positive closed zero interval. -/
public theorem high_principal_head_interval (K : HighGaussianKernel) {l r x y : ℝ} (hl : 0 < l)
    (hx : x ∈ Set.Icc l r) (hy : y ∈ Set.Icc l r) :
    ‖highPrincipalHead K y - highPrincipalHead K x‖ ≤
      (highPrincipalHeadCap K / l ^ 2) * |y - x| := by
  have he :
    highPrincipalHead K = fun t ↦
      ∫ v in (0 : ℝ)..5, principalHeadIntegrand K.realProfile K.pole 5 t v := by
    funext t
    simpa only [highPrincipalHead, Complex.ofReal_ofNat] using
      (principal_head_integral_eq K.realProfile K.pole 5 t).symm
  have hd (t : ℝ) : DifferentiableAt ℝ (highPrincipalHead K) t := by
    rw [he]
    exact (principal_head_height_deriv K.realProfile K.pole 5 t).differentiableAt
  have hder (t : ℝ) (ht : t ∈ Set.Icc l r) :
    ‖deriv (highPrincipalHead K) t‖ ≤ highPrincipalHeadCap K / l ^ 2 := by
    have ht₀ := hl.trans_le ht.1
    have h := high_principal_head_deriv_bound K ht₀.ne'
    change ‖deriv (highPrincipalHead K) t‖ ≤ highPrincipalHeadCap K / t ^ 2 at h
    exact
      h.trans
        (div_le_div_of_nonneg_left (high_principal_head_cap_nonneg K) (sq_pos_of_pos hl)
          (pow_le_pow_left₀ hl.le ht.1 _))
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_deriv_le (fun t _ ↦ hd t) hder (convex_Icc l r) hx hy

/-- On RH, the head in H25 is evaluated by its real-height function. -/
public theorem high_principal_coeff_at_height (K : HighGaussianKernel) (hRH : RiemannHypothesis)
    {ρ : ℂ} (hz : riemannZeta ρ = 0 ∧ 0 ≤ ρ.re) :
    let t := ρ.im
    let z := Complex.I * (t : ℂ)
    let s := z + (K.pole : ℂ)
    let E := Complex.exp (-(5 * (K.pole : ℂ)))
    let k :=
      (K.normalization : ℂ) * Complex.exp (5 * z) * (K.polynomial.eval₂ (Rat.castHom ℂ) s) ^ 2 /
        s ^ (2 * K.degree + 4)
    E * highPrincipalFiniteCoeff K ρ =
      (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℂ) *
        (-3 * k + 4 * highPrincipalHead K t + 4 * (E * (K.realProfile.eval 5 : ℝ)) / ρ) := by
  have hxi := AnalyticNumberTheory.RiemannXi.xi_zero_of_zeta_zero_of_re_nonneg hz.1 hz.2
  have hr := AnalyticNumberTheory.RiemannXi.xi_zero_re_eq_half_of_riemannHypothesis hRH hxi
  have hρ : ρ ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hr
    norm_num only at hr
  have he : ρ - (1 / 2 : ℂ) = Complex.I * (ρ.im : ℂ) := by
    apply Complex.ext
    · norm_num only [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im, hr, mul_zero, zero_mul, sub_zero, Complex.div_re, Complex.one_re,
        Complex.one_im, Complex.re_ofNat, Complex.im_ofNat, Complex.normSq_ofNat]
    · norm_num only [Complex.sub_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, zero_mul, Complex.div_im, Complex.one_re, Complex.one_im,
        Complex.re_ofNat, Complex.im_ofNat, Complex.normSq_ofNat, one_mul, zero_add, add_zero,
        sub_zero]
  have h := high_principal_coeff_log K hz hρ
  dsimp only at h ⊢
  rw [he] at h
  simpa only [highPrincipalHead, mul_assoc, add_comm (Complex.I * (ρ.im : ℂ)),
    Complex.ofReal_ratCast] using h

/-- The middle term in H25 has derivative norm `|w| / (t^2 + 1/4)`. -/
public theorem principal_edge_deriv_norm (w t : ℝ) :
    ‖deriv (fun u : ℝ ↦ (w : ℂ) / ((1 / 2 : ℂ) + Complex.I * u)) t‖ = |w| / (t ^ 2 + 1 / 4) := by
  let z := fun u : ℝ ↦ (1 / 2 : ℂ) + Complex.I * u
  have hz : (z t).re = 1 / 2 := by
    simp only [z, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
    norm_num only [Complex.div_re, Complex.one_re, Complex.one_im, Complex.re_ofNat,
      Complex.im_ofNat, Complex.normSq_ofNat]
  have hn : z t ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hz
    norm_num only at hz
  have h :=
    ((Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_id t)).const_mul
          Complex.I).const_add
      (1 / 2 : ℂ)
  have hd : HasDerivAt z Complex.I t := by
    simpa only [z, Function.comp_apply, id_eq, Complex.ofRealCLM_apply, Complex.ofReal_one,
      mul_one] using h
  have hdiv := (hasDerivAt_const t (w : ℂ)).div hd hn
  change ‖deriv ((fun _ : ℝ ↦ (w : ℂ)) / z) t‖ = _
  rw [hdiv.deriv, zero_mul, zero_sub, norm_div, norm_neg, norm_mul, Complex.norm_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs, norm_pow, ← Complex.normSq_eq_norm_sq]
  have him : (z t).im = t := by
    simp only [z, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, one_mul, zero_add]
    norm_num only [Complex.div_im, Complex.one_re, Complex.one_im, Complex.re_ofNat,
      Complex.im_ofNat, Complex.normSq_ofNat, mul_zero, zero_mul, sub_zero, zero_div, zero_add]
  rw [Complex.normSq_apply, hz, him]
  congr 1
  ring

end PseudoPrime.PrimeTestBounds.MillerRabin
