/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.MellinKernelForwardTransform
public import PseudoPrime.LLS.MethodBarrier.IndexSixFourier

/-!
# The sextic barrier for every admissible Mellin kernel

This file connects the existing `MellinKernel` hypotheses and the exact
Proposition 6.1 denominator to the Fourier-method obstruction. The forward
Mellin identity, the Fourier witness, and every normalization identity are
proved; they are not additional hypotheses on the kernel.

The conclusion restricts the coefficient supplied by Proposition 6.1 with
the existing common zero-cost estimate. It is not a disproof of the prime
bound asserted in LLS Theorem 1.3.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements.MellinKernel

/-- The Fourier normalization factor is positive because pi is positive. -/
private theorem two_pi_pos : 0 < 2 * Real.pi :=
  mul_pos (by norm_num only) Real.pi_pos

/-- A positive cutoff makes the logarithmic change-of-variable factor positive. -/
private theorem two_pi_sqrt_pos {lambda : ℝ} (hlambda : 0 < lambda) :
    0 < 2 * Real.pi * Real.sqrt lambda :=
  mul_pos two_pi_pos (Real.sqrt_pos.mpr hlambda)

open MeasureTheory Set Filter in
open scoped Topology FourierTransform in
open PseudoPrime.LLS.IndexSixBarrier in
/-- The logarithmic change of variables associated to a positive cutoff. -/
noncomputable def expScale (lambda t : ℝ) : ℝ :=
  lambda * Real.exp (2 * Real.pi * t)

open MeasureTheory Set Filter in
open scoped Topology FourierTransform in
open PseudoPrime.LLS.IndexSixBarrier in
/-- The positive logarithmic density of the Mellin weight. -/
noncomputable def logDensity (K : MellinKernel) (lambda t : ℝ) : ℝ :=
  (K.transform (expScale lambda t)).re * Real.exp (Real.pi * t)

open MeasureTheory Set Filter in
open scoped Topology FourierTransform in
open PseudoPrime.LLS.IndexSixBarrier in
/-- A Mellin kernel becomes an admissible Fourier witness after modulation. -/
noncomputable def fourierWitness (K : MellinKernel) (lambda x : ℝ) : ℂ :=
  (1 / (2 * Real.pi) : ℝ) • (K.function (Complex.I * x) * (lambda : ℂ) ^ (-(Complex.I * x)))

open MeasureTheory Set Filter in
open scoped Topology FourierTransform in
open PseudoPrime.LLS.IndexSixBarrier in
/-- Positive cutoffs make the exponential change of variables positive everywhere. -/
theorem expScale_pos {lambda : ℝ} (hlambda : 0 < lambda) (t : ℝ) : 0 < expScale lambda t :=
  mul_pos hlambda (Real.exp_pos _)

open MeasureTheory Set Filter in
open scoped Topology FourierTransform in
open PseudoPrime.LLS.IndexSixBarrier in
/-- The modulated critical-line witness is integrable by the kernel decay bound. -/
theorem integrable_fourierWitness (K : MellinKernel) {lambda : ℝ} (hlambda : 0 < lambda) :
    Integrable (fourierWitness K lambda) := by
  have hi :=
    K.mellin_integrable 0 lambda (by norm_num only) (by linarith only [K.delta_pos]) hlambda
  change
    Integrable
      (fun x : ℝ ↦
        (1 / (2 * Real.pi) : ℝ) • (K.function (Complex.I * x) * (lambda : ℂ) ^ (-(Complex.I * x))))
  simpa only [Complex.ofReal_zero, zero_add, Pi.smul_apply] using! hi.smul (1 / (2 * Real.pi) : ℝ)

open MeasureTheory Set Filter in
open scoped Topology FourierTransform in
open PseudoPrime.LLS.IndexSixBarrier in
/-- Unit complex modulation preserves the critical-line kernel norm. -/
theorem norm_fourierWitness (K : MellinKernel) {lambda : ℝ} (hlambda : 0 < lambda) (x : ℝ) :
    ‖fourierWitness K lambda x‖ = (1 / (2 * Real.pi)) * ‖K.function (Complex.I * x)‖ := by
  have hp := norm_mellin_power (c := 0) (u := lambda) (t := x) hlambda
  simp only [Complex.ofReal_zero, zero_add, neg_zero, Real.rpow_zero] at hp
  rw [fourierWitness, norm_smul, Real.norm_eq_abs,
    abs_of_pos (div_pos (by norm_num only) two_pi_pos), norm_mul, hp, mul_one]

open MeasureTheory Set Filter in
open scoped Topology FourierTransform in
open PseudoPrime.LLS.IndexSixBarrier in
/-- At positive cutoffs the Fourier witness L1 mass equals the Mellin kernel mass. -/
theorem l1Mass_fourierWitness (K : MellinKernel) {lambda : ℝ} (hlambda : 0 < lambda) :
    l1Mass (fourierWitness K lambda) = K.mass := by
  unfold l1Mass mass
  simp_rw [norm_fourierWitness K hlambda]
  rw [integral_const_mul]
  ring

open MeasureTheory Set Filter in
open scoped Topology FourierTransform in
open PseudoPrime.LLS.IndexSixBarrier in
private theorem fourier_phase_mul {lambda : ℝ} (hlambda : 0 < lambda) (x t : ℝ) :
    Complex.exp ((↑(-2 * Real.pi * (x * t)) : ℂ) * Complex.I) * (lambda : ℂ) ^ (-(Complex.I * x)) =
      (expScale lambda t : ℂ) ^ (-(Complex.I * x)) := by
  have hv := expScale_pos hlambda t
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hlambda.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hv.ne'), ←
    Complex.ofReal_log hlambda.le, ← Complex.ofReal_log hv.le, ← Complex.exp_add]
  congr 1
  rw [expScale, Real.log_mul hlambda.ne' (Real.exp_ne_zero _), Real.log_exp]
  simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_neg]
  ring

open MeasureTheory Set Filter in
open scoped Topology FourierTransform in
open PseudoPrime.LLS.IndexSixBarrier in
/-- Exact Fourier transform of the modulated Mellin kernel. -/
theorem fourier_fourierWitness (K : MellinKernel) {lambda : ℝ} (hlambda : 0 < lambda) (t : ℝ) :
    𝓕 (fourierWitness K lambda) t = K.transform (expScale lambda t) := by
  rw [Real.fourier_eq', transform, inverseMellin]
  simp only [fourierWitness, Complex.ofReal_zero, zero_add, Complex.real_smul, smul_eq_mul,
    Real.inner_apply]
  rw [← integral_const_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  calc
    _ =
        ((1 / (2 * Real.pi) : ℝ) : ℂ) * K.function (Complex.I * x) *
          (Complex.exp ((↑(-2 * Real.pi * (x * t)) : ℂ) * Complex.I) *
            (lambda : ℂ) ^ (-(Complex.I * x))) :=
      by ring
    _ = _ := by
      rw [fourier_phase_mul hlambda]; ring

open MeasureTheory Set Filter in
open scoped Topology FourierTransform in
open PseudoPrime.LLS.IndexSixBarrier in
/-- Mellin positivity and the forward identity make the witness Fourier real part nonnegative. -/
theorem fourier_fourierWitness_nonneg (K : MellinKernel) {lambda : ℝ} (hlambda : 0 < lambda)
    (t : ℝ) : 0 ≤ (𝓕 (fourierWitness K lambda) t).re := by
  rw [fourier_fourierWitness K hlambda]
  exact K.mellin_nonneg _ (expScale_pos hlambda t)

open MeasureTheory Set Filter in
open scoped Topology FourierTransform in
open PseudoPrime.LLS.IndexSixBarrier in
private theorem hasDerivAt_expScale (lambda t : ℝ) :
    HasDerivAt (expScale lambda) (2 * Real.pi * expScale lambda t) t := by
  change
    HasDerivAt (fun x : ℝ ↦ lambda * Real.exp (2 * Real.pi * x))
      (2 * Real.pi * (lambda * Real.exp (2 * Real.pi * t))) t
  convert!
    (((Real.hasDerivAt_exp (2 * Real.pi * t)).comp t
          ((hasDerivAt_id t).const_mul (2 * Real.pi))).const_mul
      lambda) using
    1
  ring

open MeasureTheory Set Filter in
open scoped Topology FourierTransform in
open PseudoPrime.LLS.IndexSixBarrier in
private theorem expScale_injective {lambda : ℝ} (hlambda : 0 < lambda) :
    Function.Injective (expScale lambda) := by
  intro x y hxy
  have he : Real.exp (2 * Real.pi * x) = Real.exp (2 * Real.pi * y) :=
    mul_left_cancel₀ hlambda.ne' hxy
  exact mul_left_cancel₀ (two_pi_pos.ne') (Real.exp_injective he)

open MeasureTheory Set Filter in
open scoped Topology FourierTransform in
open PseudoPrime.LLS.IndexSixBarrier in
private theorem expScale_log_div {lambda u : ℝ} (hlambda : 0 < lambda) (hu : 0 < u) :
    expScale lambda (Real.log (u / lambda) / (2 * Real.pi)) = u := by
  unfold expScale
  rw [mul_div_cancel₀ _ (two_pi_pos.ne'), Real.exp_log (div_pos hu hlambda)]
  field_simp

open MeasureTheory Set Filter in
open scoped Topology FourierTransform in
open PseudoPrime.LLS.IndexSixBarrier in
private theorem image_expScale_univ {lambda : ℝ} (hlambda : 0 < lambda) :
    expScale lambda '' univ = Ioi 0 := by
  ext u
  constructor
  · rintro ⟨t, _, rfl⟩
    exact expScale_pos hlambda t
  · intro hu
    exact ⟨Real.log (u / lambda) / (2 * Real.pi), mem_univ _, expScale_log_div hlambda hu⟩

open MeasureTheory Set Filter in
open scoped Topology FourierTransform in
open PseudoPrime.LLS.IndexSixBarrier in
private theorem image_expScale_Iic {lambda : ℝ} (hlambda : 0 < lambda) :
    expScale lambda '' Iic 0 = Ioc 0 lambda := by
  ext u
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨expScale_pos hlambda t, ?_⟩
    calc
      expScale lambda t ≤ lambda * 1 :=
        mul_le_mul_of_nonneg_left
          (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos two_pi_pos.le ht)) hlambda.le
      _ = lambda := mul_one _
  · intro hu
    refine ⟨Real.log (u / lambda) / (2 * Real.pi), ?_, expScale_log_div hlambda hu.1⟩
    exact
      div_nonpos_of_nonpos_of_nonneg
        (Real.log_nonpos (div_nonneg hu.1.le hlambda.le) ((div_le_one hlambda).mpr hu.2))
        two_pi_pos.le

open MeasureTheory Set Filter in
open scoped Topology FourierTransform in
open PseudoPrime.LLS.IndexSixBarrier in
private theorem sqrt_expScale {lambda : ℝ} (hlambda : 0 < lambda) (t : ℝ) :
    Real.sqrt (expScale lambda t) = Real.sqrt lambda * Real.exp (Real.pi * t) := by
  rw [expScale, Real.sqrt_mul hlambda.le, Real.sqrt_eq_rpow (Real.exp _),
    Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  congr 2
  ring

open MeasureTheory Set Filter in
open scoped Topology FourierTransform in
open PseudoPrime.LLS.IndexSixBarrier in
private theorem expScale_jacobian_weight (K : MellinKernel) {lambda : ℝ} (hlambda : 0 < lambda)
    (t : ℝ) :
    |2 * Real.pi * expScale lambda t| •
        ((K.transform (expScale lambda t)).re / Real.sqrt (expScale lambda t)) =
      (2 * Real.pi * Real.sqrt lambda) * logDensity K lambda t := by
  rw [abs_of_pos (mul_pos two_pi_pos (expScale_pos hlambda t)), smul_eq_mul]
  have hs := Real.sq_sqrt (expScale_pos hlambda t).le
  rw [sqrt_expScale hlambda] at hs ⊢
  unfold logDensity
  conv_lhs =>
    lhs; rw [← hs]
  field_simp (disch :=
    first
    | exact (Real.sqrt_pos.mpr hlambda).ne'
    | exact Real.exp_ne_zero _
    | norm_num only)

open MeasureTheory Set Filter in
open scoped Topology FourierTransform in
open PseudoPrime.LLS.IndexSixBarrier in
private theorem integral_image_expScale_weight (K : MellinKernel) {lambda : ℝ}
    (hlambda : 0 < lambda) {s : Set ℝ} (hs : MeasurableSet s) :
    (∫ u in expScale lambda '' s, (K.transform u).re / Real.sqrt u) =
      (2 * Real.pi * Real.sqrt lambda) * (∫ t in s, logDensity K lambda t) := by
  rw [integral_image_eq_integral_abs_deriv_smul hs
      (fun t _ ↦ (hasDerivAt_expScale lambda t).hasDerivWithinAt)
      (expScale_injective hlambda).injOn]
  simp_rw [expScale_jacobian_weight K hlambda]
  exact integral_const_mul _ _

open MeasureTheory Set Filter in
open scoped Topology FourierTransform in
open PseudoPrime.LLS.IndexSixBarrier in
/-- The logarithmic change of variables preserves weighted Mellin integrability. -/
theorem integrable_logDensity (K : MellinKernel) {lambda : ℝ} (hlambda : 0 < lambda) :
    Integrable (logDensity K lambda) := by
  have hi :=
    integrableOn_image_iff_integrableOn_abs_deriv_smul (s := univ) MeasurableSet.univ
      (fun t _ ↦ (hasDerivAt_expScale lambda t).hasDerivWithinAt) (expScale_injective hlambda).injOn
      (fun u : ℝ ↦ (K.transform u).re / Real.sqrt u)
  rw [image_expScale_univ hlambda, integrableOn_univ] at hi
  have hp := hi.mp (integrableOn_weight_Ioi K)
  simp_rw [expScale_jacobian_weight K hlambda] at hp
  exact (integrable_smul_iff ((two_pi_sqrt_pos hlambda).ne') _).mp hp

open MeasureTheory Set Filter in
open scoped Topology FourierTransform in
open PseudoPrime.LLS.IndexSixBarrier in
/-- The full logarithmic density integral equals the real Mellin endpoint value. -/
theorem integral_logDensity (K : MellinKernel) {lambda : ℝ} (hlambda : 0 < lambda) :
    (∫ t, logDensity K lambda t) = (K.function (1 / 2)).re / (2 * Real.pi * Real.sqrt lambda) := by
  have hi := integral_image_expScale_weight K hlambda (s := univ) MeasurableSet.univ
  rw [image_expScale_univ hlambda, integral_weight_Ioi_eq K, setIntegral_univ] at hi
  apply (eq_div_iff ((two_pi_sqrt_pos hlambda).ne')).mpr
  linarith only [hi]

open MeasureTheory Set Filter in
open scoped Topology FourierTransform in
open PseudoPrime.LLS.IndexSixBarrier in
/-- The negative-half-line logarithmic density integral equals the truncated Mellin weight. -/
theorem integral_logDensity_Iic (K : MellinKernel) {lambda : ℝ} (hlambda : 0 < lambda) :
    (∫ t in Iic 0, logDensity K lambda t) =
      (∫ u in (0 : ℝ)..lambda, (K.transform u).re / Real.sqrt u) /
        (2 * Real.pi * Real.sqrt lambda) := by
  have hi := integral_image_expScale_weight K hlambda (s := Iic (0 : ℝ)) measurableSet_Iic
  rw [image_expScale_Iic hlambda, ← intervalIntegral.integral_of_le hlambda.le] at hi
  apply (eq_div_iff ((two_pi_sqrt_pos hlambda).ne')).mpr
  linarith only [hi]

open MeasureTheory Set Filter in
open scoped Topology FourierTransform in
open PseudoPrime.LLS.IndexSixBarrier in
private theorem ep1Integrand_fourierWitness (K : MellinKernel) {lambda : ℝ} (hlambda : 0 < lambda) :
    ep1Integrand (fourierWitness K lambda) = fun t ↦
      (6 / 5 : ℝ) * (Iic 0).indicator (logDensity K lambda) t -
        (1 / 5 : ℝ) * logDensity K lambda t := by
  funext t
  have hn : 0 ≤ (K.transform (expScale lambda t)).re := K.mellin_nonneg _ (expScale_pos hlambda t)
  by_cases ht : t ≤ 0
  · simp only [ep1Integrand, ht, fourier_fourierWitness K hlambda, ite_true, Set.indicator_apply,
      Set.mem_Iic, logDensity]
    ring
  · simp only [ep1Integrand, ht, fourier_fourierWitness K hlambda, max_eq_right (neg_nonpos.mpr hn),
      max_eq_left hn, zero_add, ite_false, Set.indicator_apply, Set.mem_Iic, logDensity]
    ring

open MeasureTheory Set Filter in
open scoped Topology FourierTransform in
open PseudoPrime.LLS.IndexSixBarrier in
/-- Both half-line terms of the witness EP1 numerator are integrable. -/
theorem integrable_ep1Integrand_fourierWitness (K : MellinKernel) {lambda : ℝ}
    (hlambda : 0 < lambda) : Integrable (ep1Integrand (fourierWitness K lambda)) := by
  rw [ep1Integrand_fourierWitness K hlambda]
  exact
    (((integrable_logDensity K hlambda).indicator measurableSet_Iic).const_mul _).sub
      ((integrable_logDensity K hlambda).const_mul _)

open MeasureTheory Set Filter in
open scoped Topology FourierTransform in
open PseudoPrime.LLS.IndexSixBarrier in
/-- The central sextic denominator in the existing Proposition 6.1. -/
noncomputable def indexSixDenominator (K : MellinKernel) (lambda : ℝ) : ℝ :=
  6 * (∫ u in (0 : ℝ)..lambda, (K.transform u).re / Real.sqrt u) - (K.function (1 / 2)).re

open MeasureTheory Set Filter in
open scoped Topology FourierTransform in
open PseudoPrime.LLS.IndexSixBarrier in
/-- The EP1 numerator equals the sextic denominator divided by 10*pi*sqrt(lambda). -/
theorem ep1Numerator_fourierWitness (K : MellinKernel) {lambda : ℝ} (hlambda : 0 < lambda) :
    ep1Numerator (fourierWitness K lambda) =
      indexSixDenominator K lambda / (10 * Real.pi * Real.sqrt lambda) := by
  rw [ep1Numerator, ep1Integrand_fourierWitness K hlambda,
    integral_sub (((integrable_logDensity K hlambda).indicator measurableSet_Iic).const_mul _)
      ((integrable_logDensity K hlambda).const_mul _),
    integral_const_mul, integral_const_mul, integral_indicator measurableSet_Iic,
    integral_logDensity_Iic K hlambda, integral_logDensity K hlambda]
  unfold indexSixDenominator
  field_simp (disch :=
    first
    | exact Real.pi_ne_zero
    | exact (Real.sqrt_pos.mpr hlambda).ne'
    | norm_num only)
  ring

open MeasureTheory Set Filter in
open scoped Topology FourierTransform in
open PseudoPrime.LLS.IndexSixBarrier in
/-- The leading squared-log coefficient obtained by solving Proposition 6.1
at index six, before the arbitrarily small error inflation. -/
noncomputable def indexSixMethodCoefficient (K : MellinKernel) (lambda : ℝ) : ℝ :=
  lambda * (5 * K.mass / indexSixDenominator K lambda) ^ 2

open MeasureTheory Set Filter in
open scoped Topology FourierTransform in
open PseudoPrime.LLS.IndexSixBarrier in
/-- Positive cutoffs and denominators identify the EP1 and sextic Mellin coefficients. -/
theorem ep1Coefficient_fourierWitness (K : MellinKernel) {lambda : ℝ} (hlambda : 0 < lambda)
    (hdenom : 0 < indexSixDenominator K lambda) :
    ep1Coefficient (fourierWitness K lambda) = indexSixMethodCoefficient K lambda := by
  rw [ep1Coefficient, l1Mass_fourierWitness K hlambda, ep1Numerator_fourierWitness K hlambda]
  have he :
    K.mass / (2 * Real.pi * (indexSixDenominator K lambda / (10 * Real.pi * Real.sqrt lambda))) =
      Real.sqrt lambda * (5 * K.mass / indexSixDenominator K lambda) := by
    field_simp (disch :=
      first
      | exact hdenom.ne'
      | exact Real.pi_ne_zero
      | exact (Real.sqrt_pos.mpr hlambda).ne'
      | norm_num only)
    ring
  rw [he, mul_pow, Real.sq_sqrt hlambda.le]
  rfl

open MeasureTheory Set Filter in
open scoped Topology FourierTransform in
open PseudoPrime.LLS.IndexSixBarrier in
/-- No admissible Mellin kernel and positive cutoff can make the leading
Proposition 6.1 coefficient at index six smaller than `60 / 121`. -/
theorem indexSixMethodCoefficient_ge (K : MellinKernel) {lambda : ℝ} (hlambda : 0 < lambda)
    (hdenom : 0 < indexSixDenominator K lambda) :
    (60 / 121 : ℝ) ≤ indexSixMethodCoefficient K lambda := by
  rw [← ep1Coefficient_fourierWitness K hlambda hdenom]
  apply ep1_coefficient_ge
  · exact integrable_fourierWitness K hlambda
  · exact integrable_ep1Integrand_fourierWitness K hlambda
  · rw [ep1Numerator_fourierWitness K hlambda]
    exact
      div_pos hdenom (mul_pos (mul_pos (by norm_num only) Real.pi_pos) (Real.sqrt_pos.mpr hlambda))

open MeasureTheory Set Filter in
open scoped Topology FourierTransform in
open PseudoPrime.LLS.IndexSixBarrier in
/-- Searching the full existing admissible-kernel type cannot meet the paper
target at this one positive epsilon. -/
theorem no_mellin_certificate_at_paper_target :
    ¬∃ (K : MellinKernel) (lambda : ℝ),
        0 < lambda ∧
          0 < indexSixDenominator K lambda ∧
          indexSixMethodCoefficient K lambda ≤ paperCoefficient (1 / 200) := by
  rintro ⟨K, lambda, hlambda, hdenom, hc⟩
  exact
    (not_le_of_gt paperCoefficient_one_div_two_hundred_lt_barrier)
      ((indexSixMethodCoefficient_ge K hlambda hdenom).trans hc)

open MeasureTheory Set Filter in
open scoped Topology FourierTransform in
open PseudoPrime.LLS.IndexSixBarrier in
/-- Refining a rational upper certificate with any denominator cannot overcome
the same obstruction for any admissible Mellin kernel. -/
theorem no_rational_mellin_certificate_at_paper_target :
    ¬∃ (K : MellinKernel) (lambda : ℝ) (r : ℚ),
        0 < lambda ∧
          0 < indexSixDenominator K lambda ∧
          indexSixMethodCoefficient K lambda ≤ (r : ℝ) ∧ (r : ℝ) ≤ paperCoefficient (1 / 200) := by
  rintro ⟨K, lambda, r, hlambda, hdenom, hr, hc⟩
  exact no_mellin_certificate_at_paper_target ⟨K, lambda, hlambda, hdenom, hr.trans hc⟩

open MeasureTheory Set Filter in
open scoped Topology FourierTransform in
open PseudoPrime.LLS.IndexSixBarrier in
/-- The kernel method cannot supply the paper's coefficient for every positive
epsilon, even if both the kernel and the cutoff may depend on epsilon. -/
theorem not_mellin_certificates_for_all_positive_epsilon :
    ¬(∀ ε : ℝ,
        0 < ε →
          ∃ (K : MellinKernel) (lambda : ℝ),
            0 < lambda ∧
              0 < indexSixDenominator K lambda ∧
              indexSixMethodCoefficient K lambda ≤ paperCoefficient ε) := by
  intro h
  exact no_mellin_certificate_at_paper_target (h (1 / 200) (by norm_num only))

end PseudoPrime.LLS.PaperStatements.MellinKernel
