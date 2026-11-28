/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianPrincipalLowZeros
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianPrincipalHeadDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.Ring

/-! # Boundary cancellation for the principal Gaussian zero tail -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Two integrations by parts isolate the boundary term of the finite Fourier integral.
The amplitude and its first derivative vanish at the left endpoint. -/
private theorem principal_fourier_second_identity {f f₁ f₂ : ℝ → ℂ} {b : ℝ} (c : ℂ)
    (hf : Continuous f) (hf₁ : Continuous f₁) (hf₂ : Continuous f₂)
    (hd : ∀ v, HasDerivAt f (f₁ v) v) (hd₁ : ∀ v, HasDerivAt f₁ (f₂ v) v) (h₀ : f 0 = 0)
    (h₁ : f₁ 0 = 0) :
    let p := fun v : ℝ ↦ Complex.exp (c * (v : ℂ))
    c ^ 2 * (∫ v in (0 : ℝ)..b, f v * p v) =
      c * f b * p b - f₁ b * p b + ∫ v in (0 : ℝ)..b, f₂ v * p v := by
  intro p
  have hp : Continuous p := by
    unfold p; fun_prop
  have hpd (v : ℝ) : HasDerivAt p (c * p v) v := by
    have h := (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt v (hasDerivAt_id v)).const_mul c
    simpa only [p, Function.comp_apply, id_eq, Complex.ofRealCLM_apply, Complex.ofReal_one, mul_one,
      mul_comm] using h.cexp
  have hi := (hp.const_mul c).intervalIntegrable (μ := MeasureTheory.volume) 0 b
  have hA :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt hf.continuousOn hp.continuousOn
      (fun v _ ↦ hd v) (fun v _ ↦ hpd v) (hf₁.intervalIntegrable _ _) hi
  have hB :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt hf₁.continuousOn hp.continuousOn
      (fun v _ ↦ hd₁ v) (fun v _ ↦ hpd v) (hf₂.intervalIntegrable _ _) hi
  have pull (g : ℝ → ℂ) :
    (∫ v in (0 : ℝ)..b, g v * (c * p v)) = c * ∫ v in (0 : ℝ)..b, g v * p v := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr (fun v _ ↦ mul_left_comm _ _ _)
  rw [pull f, h₀, zero_mul, sub_zero] at hA
  rw [pull f₁, h₁, zero_mul, sub_zero] at hB
  rw [pow_two, mul_assoc, hA, mul_sub, hB]
  ring

/-- After removing the right endpoint term, the Fourier head decays quadratically. -/
public theorem principal_fourier_remainder_le {f f₁ f₂ : ℝ → ℂ} {b t : ℝ} (hb : 0 ≤ b) (ht : t ≠ 0)
    (hf : Continuous f) (hf₁ : Continuous f₁) (hf₂ : Continuous f₂)
    (hd : ∀ v, HasDerivAt f (f₁ v) v) (hd₁ : ∀ v, HasDerivAt f₁ (f₂ v) v) (h₀ : f 0 = 0)
    (h₁ : f₁ 0 = 0) :
    let c := -Complex.I * (t : ℂ)
    let p := fun v : ℝ ↦ Complex.exp (c * (v : ℂ))
    let q := Complex.exp (-(c * b))
    ‖q * (∫ v in (0 : ℝ)..b, f v * p v) - f b / c‖ ≤
      (‖f₁ b‖ + ∫ v in (0 : ℝ)..b, ‖f₂ v‖) / t ^ 2 := by
  intro c p q
  have hcn : ‖c‖ = |t| := by
    simp only [c, norm_mul, norm_neg, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, one_mul]
  have hc : c ≠ 0 := fun h ↦ ht (abs_eq_zero.mp (hcn.symm.trans (h ▸ norm_zero)))
  have hp (v : ℝ) : ‖p v‖ = 1 := by
    unfold p c
    simp only [Complex.norm_exp, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul,
      sub_zero, neg_zero, Real.exp_zero]
  have hq : ‖q‖ = 1 := by
    change ‖Complex.exp (-(c * (b : ℂ)))‖ = 1
    rw [Complex.exp_neg, norm_inv, hp b, inv_one]
  have hqp : q * p b = 1 := by
    dsimp only [q, p]
    rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  have he : c ^ 2 * (f b / c) = c * f b := by
    rw [pow_two, mul_assoc, ← mul_div_assoc, mul_div_cancel_left₀ _ hc]
  have h := principal_fourier_second_identity (b := b) c hf hf₁ hf₂ hd hd₁ h₀ h₁
  change
    c ^ 2 * (∫ v in (0 : ℝ)..b, f v * p v) =
      c * f b * p b - f₁ b * p b + ∫ v in (0 : ℝ)..b, f₂ v * p v at h
  have hh :
    c ^ 2 * (q * (∫ v in (0 : ℝ)..b, f v * p v) - f b / c) =
      -(f₁ b) + q * (∫ v in (0 : ℝ)..b, f₂ v * p v) := by
    rw [mul_sub, he, mul_left_comm, h, mul_add, mul_sub]
    have he₁ : q * (c * f b * p b) = c * f b := by
      calc
        _ = (c * f b) * (q * p b) := by ring
        _ = _ := by rw [hqp, mul_one]
    have he₂ : q * (f₁ b * p b) = f₁ b := by rw [mul_left_comm, hqp, mul_one]
    rw [he₁, he₂]
    ring
  have hi :=
    intervalIntegral.norm_integral_le_integral_norm (a := 0) (b := b) (μ := MeasureTheory.volume)
      (f := fun v ↦ f₂ v * p v) hb
  have hi' : ‖∫ v in (0 : ℝ)..b, f₂ v * p v‖ ≤ ∫ v in (0 : ℝ)..b, ‖f₂ v‖ := by
    refine hi.trans_eq (intervalIntegral.integral_congr (fun v _ ↦ ?_))
    rw [norm_mul, hp, mul_one]
  apply (le_div_iff₀ (sq_pos_of_ne_zero ht)).mpr
  rw [mul_comm, ← sq_abs, ← hcn, ← norm_pow, ← norm_mul, hh]
  have hqi : ‖q * (∫ v in (0 : ℝ)..b, f₂ v * p v)‖ = ‖∫ v in (0 : ℝ)..b, f₂ v * p v‖ := by
    rw [norm_mul, hq, one_mul]
  exact (norm_add_le _ _).trans (add_le_add (norm_neg _).le (hqi.trans_le hi'))

/-- The two boundary reciprocals cancel to a term of order inverse height squared. -/
private theorem principal_edge_cancel_le (w : ℂ) {t : ℝ} (ht : t ≠ 0) :
    ‖w / (-Complex.I * (t : ℂ)) + w / (1 / 2 + Complex.I * (t : ℂ))‖ ≤ (‖w‖ / 2) / t ^ 2 := by
  let z := Complex.I * (t : ℂ)
  have hz : z ≠ 0 := mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr ht)
  have hhalf : ((1 / 2 : ℝ) : ℂ) = 1 / 2 := by
    simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  have him : ((1 / 2 : ℂ) + z).im = t := by
    rw [← hhalf]
    simp only [z, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_im,
      Complex.ofReal_re, zero_mul, one_mul, zero_add]
  have hn : (1 / 2 : ℂ) + z ≠ 0 := by
    intro h
    apply ht
    rw [← him, h, Complex.zero_im]
  have cancel (b : ℂ) (hb : b + z ≠ 0) : w / (-z) + w / (b + z) = -(w * b) / (z * (b + z)) := by
    field_simp [hz, hb]
    ring
  have he : w / (-z) + w / (1 / 2 + z) = -(w / 2) / (z * (1 / 2 + z)) := by
    simpa only [mul_one_div] using cancel (1 / 2) hn
  have hzN : ‖z‖ = |t| := by
    simp only [z, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, one_mul]
  have hd : t ^ 2 ≤ ‖z * (1 / 2 + z)‖ := by
    rw [norm_mul, hzN, ← sq_abs, pow_two, ← him]
    exact mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm _) (abs_nonneg _)
  rw [neg_mul, he, norm_div, norm_neg, norm_div, Complex.norm_ofNat]
  exact
    div_le_div_of_nonneg_left (div_nonneg (norm_nonneg _) (by norm_num only)) (sq_pos_of_ne_zero ht)
      hd

/-- Adding the H25 middle term leaves an inverse-square bound for the finite head. -/
public theorem principal_fourier_centered_le {f f₁ f₂ : ℝ → ℂ} {b t : ℝ} (hb : 0 ≤ b) (ht : t ≠ 0)
    (hf : Continuous f) (hf₁ : Continuous f₁) (hf₂ : Continuous f₂)
    (hd : ∀ v, HasDerivAt f (f₁ v) v) (hd₁ : ∀ v, HasDerivAt f₁ (f₂ v) v) (h₀ : f 0 = 0)
    (h₁ : f₁ 0 = 0) :
    let c := -Complex.I * (t : ℂ)
    let p := fun v : ℝ ↦ Complex.exp (c * (v : ℂ))
    let q := Complex.exp (-(c * b))
    ‖q * (∫ v in (0 : ℝ)..b, f v * p v) + f b / (1 / 2 + Complex.I * (t : ℂ))‖ ≤
      (‖f₁ b‖ + (∫ v in (0 : ℝ)..b, ‖f₂ v‖) + ‖f b‖ / 2) / t ^ 2 := by
  intro c p q
  let U := q * (∫ v in (0 : ℝ)..b, f v * p v)
  change ‖U + f b / (1 / 2 + Complex.I * (t : ℂ))‖ ≤ _
  rw [← sub_add_cancel U (f b / c), add_assoc]
  exact
    (norm_add_le _ _).trans
      ((add_le_add (principal_fourier_remainder_le hb ht hf hf₁ hf₂ hd hd₁ h₀ h₁)
            (principal_edge_cancel_le (f b) ht)).trans_eq
        (add_div _ _ _).symm)

/-- The amplitude for an exponentially weighted real polynomial in the finite head. -/
private noncomputable def tailAmplitude (a : ℝ) (P : Polynomial ℝ) (v : ℝ) : ℂ :=
  Complex.ofReal (Real.exp (-a * v) * P.eval v)

/-- The derivative polynomial of an amplitude with fixed exponential rate. -/
private noncomputable def tailDerivative (a : ℝ) (P : Polynomial ℝ) : Polynomial ℝ :=
  P.derivative - Polynomial.C a * P

/-- The rational-integral ingredients for the centered finite head tail bound. -/
public noncomputable def highTailHeadCharge (K : HighGaussianKernel) : ℝ :=
  let a := (K.pole : ℝ)
  let B := K.realProfile
  let D := tailDerivative a B
  ‖tailAmplitude a D 5‖ + (∫ v in (0 : ℝ)..5, ‖tailAmplitude a (tailDerivative a D) v‖) +
    ‖tailAmplitude a B 5‖ / 2

/-- The oscillatory head combines with the middle-value term before taking norms. -/
public theorem high_centered_head_tail_le (K : HighGaussianKernel) {t : ℝ} (ht : t ≠ 0) :
    ‖highPrincipalHead K t + ((highPrincipalEdge K : ℂ) / (1 / 2 + Complex.I * (t : ℂ)))‖ ≤
      highTailHeadCharge K / t ^ 2 := by
  let a := (K.pole : ℝ)
  let B := K.realProfile
  let D := tailDerivative a B
  have hcont (P : Polynomial ℝ) : Continuous (tailAmplitude a P) := by
    unfold tailAmplitude
    fun_prop
  have h₀ : tailAmplitude a B 0 = 0 := by
    simp only [tailAmplitude, B, (high_real_profile_at_zero K).1, mul_zero, Complex.ofReal_zero]
  have h₁ : tailAmplitude a D 0 = 0 := by
    simp only [tailAmplitude, D, tailDerivative, B, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_C, (high_real_profile_at_zero K).1, (high_real_profile_at_zero K).2, mul_zero,
      sub_zero, Complex.ofReal_zero]
  have h :=
    principal_fourier_centered_le (b := 5) (by norm_num only) ht (hcont B) (hcont D)
      (hcont (tailDerivative a D)) (weighted_poly_deriv B a) (weighted_poly_deriv D a) h₀ h₁
  have hq : Complex.exp (-(-Complex.I * (t : ℂ) * 5)) = Complex.exp (5 * Complex.I * t) := by
    congr 1
    ring
  have he : tailAmplitude a B 5 = (highPrincipalEdge K : ℂ) := by
    unfold tailAmplitude highPrincipalEdge
    rw [neg_mul, neg_mul, mul_comm a]
  have hi :
    (∫ v in (0 : ℝ)..5, tailAmplitude a B v * Complex.exp (-Complex.I * (t : ℂ) * v)) =
      ∫ v in (0 : ℝ)..5,
        Complex.exp (-(v : ℂ) * ((a : ℂ) + Complex.I * t)) * Complex.ofReal (B.eval v) := by
    apply intervalIntegral.integral_congr
    intro v _
    dsimp only [tailAmplitude]
    rw [Complex.ofReal_mul, Complex.ofReal_exp, mul_right_comm, ← Complex.exp_add]
    congr 2
    simp only [Complex.ofReal_mul, Complex.ofReal_neg]
    ring
  change
    ‖Complex.exp (-(-Complex.I * (t : ℂ) * 5)) *
            (∫ v in (0 : ℝ)..5, tailAmplitude a B v * Complex.exp (-Complex.I * (t : ℂ) * v)) +
          tailAmplitude a B 5 / (1 / 2 + Complex.I * (t : ℂ))‖ ≤
      highTailHeadCharge K / t ^ 2 at h
  rw [hq, hi, he] at h
  exact h

/-- Upper bound on the multiplier after extracting the inverse square above height 100. -/
public noncomputable def highPrincipalTailCharge (K : HighGaussianKernel) : ℝ :=
  3 * (K.normalization : ℝ) * highCompactMass K ^ 2 / 100 ^ 2 + 4 * highTailHeadCharge K

/-- The compact square contributes a fourth-power tail. -/
private theorem high_square_tail_le (K : HighGaussianKernel) {t : ℝ} (ht : 0 < t) :
    ‖highHeightKernel K t‖ ≤ (K.normalization : ℝ) * highCompactMass K ^ 2 / t ^ 4 := by
  have hn : 0 ≤ (K.normalization : ℝ) := Rat.cast_nonneg.mpr (high_gaussian_normalization_pos K).le
  have hp : ‖Complex.exp (5 * Complex.I * (t : ℂ))‖ = 1 := by
    simp only [Complex.norm_exp, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, show (5 : ℂ).im = 0 from rfl, mul_zero, zero_mul,
      sub_zero, mul_one, Real.exp_zero]
  have h := (high_kernel_quot_bounds K ht).1
  have hs := pow_le_pow_left₀ (norm_nonneg _) h 2
  have hcast : ‖(K.normalization : ℂ)‖ = (K.normalization : ℝ) := by
    rw [← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hn]
  rw [highHeightKernel, norm_mul, norm_mul, hp, mul_one, hcast, norm_pow]
  exact (mul_le_mul_of_nonneg_left hs hn).trans_eq (by rw [div_pow, ← pow_mul, mul_div_assoc])

/-- The H25 multiplier has an inverse-square tail with a height-independent prefactor. -/
public theorem high_multiplier_tail_le (K : HighGaussianKernel) {t : ℝ} (ht : 100 < t) :
    ‖highPrincipalMultiplier K t‖ ≤ highPrincipalTailCharge K / t ^ 2 := by
  have ht0 := (by norm_num only : (0 : ℝ) < 100).trans ht
  have h₂ : (100 : ℝ) ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ (by norm_num only) ht.le 2
  have hn : 0 ≤ (K.normalization : ℝ) := Rat.cast_nonneg.mpr (high_gaussian_normalization_pos K).le
  have hN : 0 ≤ 3 * (K.normalization : ℝ) * highCompactMass K ^ 2 :=
    mul_nonneg (mul_nonneg (by norm_num only) hn) (sq_nonneg _)
  unfold highPrincipalMultiplier highPrincipalTailCharge
  rw [add_assoc, ← mul_add, add_div]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_mul, norm_neg, Complex.norm_ofNat]
    refine (mul_le_mul_of_nonneg_left (high_square_tail_le K ht0) (by norm_num only)).trans ?_
    rw [← mul_div_assoc, ← mul_assoc, show t ^ 4 = t ^ 2 * t ^ 2 by ring, ← div_div]
    exact
      div_le_div_of_nonneg_right (div_le_div_of_nonneg_left hN (by norm_num only) h₂) (sq_nonneg _)
  · rw [norm_mul, Complex.norm_ofNat, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (high_centered_head_tail_le K ht0.ne') (by norm_num only)

/-- The tail prefactor is a sum of nonnegative charges. -/
public theorem high_principal_tail_nonneg (K : HighGaussianKernel) :
    0 ≤ highPrincipalTailCharge K := by
  have h := (norm_nonneg _).trans (high_multiplier_tail_le K (by norm_num only : (100 : ℝ) < 101))
  have he := mul_nonneg h (by norm_num only : (0 : ℝ) ≤ 101 ^ 2)
  rwa [div_mul_cancel₀ _ (by norm_num only : (101 : ℝ) ^ 2 ≠ 0)] at he

/-- The full principal series is bounded by the low brackets and the analytic tail charge. -/
public theorem high_principal_series_tail_le (K : HighGaussianKernel) (hRH : RiemannHypothesis)
    (hc : highPrincipalHeadCap K ≤ (highHeadCapTicks K : ℝ) / 1000) {X : ℝ} (hX : 0 < X) :
    let d := (K.pole : ℝ) - 1 / 2
    let W := fun u : ℝ ↦ u ^ d * K.realProfile.eval (5 - Real.log u)
    let F := fun u : ℝ ↦ u * deriv W u
    |Real.exp (-(5 * (K.pole : ℝ))) *
          (principalErrorFunctional (deriv F) gaussianLogZetaZeroSum (F 1) X (Real.exp 5) /
            Real.sqrt X)| ≤
      2 *
          ((∑ i, ‖highPrincipalMultiplier K (highZeroBracketMid i : ℝ)‖) +
            (highZeroErrorBudget K : ℝ)) +
        highPrincipalTailCharge K * (13 / 1000) := by
  exact
    high_principal_series_le K hRH (high_principal_tail_nonneg K) hc
      (fun _ ht ↦ high_multiplier_tail_le K ht) hX

end PseudoPrime.PrimeTestBounds.MillerRabin
