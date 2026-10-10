/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.MellinKernelTransformRegularity
public import Mathlib.Analysis.MellinInversion
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Forward Mellin reconstruction from vertical-line kernel hypotheses

The forward Mellin identity is derived from the existing vertical-line hypotheses;
it is not introduced as an additional assumption on an admissible kernel.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements.MellinKernel

open MeasureTheory Set Filter in
open scoped Topology FourierTransform in
/-- The inverse transform has the power decay of any allowed vertical line. -/
theorem isBigO_transform_rpow_atTop (K : MellinKernel) {c : ℝ} (hc : -1 / 2 < c)
    (hc' : c ≤ 1 / 2 + K.delta) : K.transform =O[atTop] (fun u : ℝ ↦ u ^ (-c)) := by
  refine
    Asymptotics.IsBigO.of_bound
      ((1 / (2 * Real.pi)) * ∫ t : ℝ, ‖K.function ((c : ℂ) + Complex.I * t)‖) ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with u hu
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hu.le _)] using
    norm_transform_le_line K hc hc' hu

open MeasureTheory Set Filter in
open scoped Topology FourierTransform in
/-- On the positive side of zero, the inverse transform is bounded by the mass. -/
theorem isBigO_transform_one_atZero (K : MellinKernel) :
    K.transform =O[𝓝[>] 0] (fun u : ℝ ↦ u ^ (-(0 : ℝ))) := by
  refine Asymptotics.IsBigO.of_bound K.mass ?_
  filter_upwards [self_mem_nhdsWithin] with u hu
  simpa only [neg_zero, Real.rpow_zero, norm_one, mul_one] using norm_transform_le_mass K hu

open MeasureTheory Set Filter in
open scoped Topology FourierTransform in
/-- The transform has a genuinely convergent Mellin integral throughout the
positive part of the strip. This uses two allowed inverse-Mellin lines. -/
theorem mellinConvergent_transform (K : MellinKernel) {s : ℂ} (hs : 0 < s.re)
    (hs' : s.re < 1 / 2 + K.delta) : MellinConvergent K.transform s := by
  exact
    mellinConvergent_of_isBigO_rpow
      ((continuousOn_transform K).locallyIntegrableOn measurableSet_Ioi)
      (isBigO_transform_rpow_atTop K
        (by linarith only [K.delta_pos] : -(1 : ℝ) / 2 < 1 / 2 + K.delta) le_rfl)
      hs' (isBigO_transform_one_atZero K) hs

open MeasureTheory Set Filter in
open scoped Topology FourierTransform in
/-- Match the project's multiplication convention with mathlib's Mellin inverse. -/
theorem mellinInv_eq_transform (K : MellinKernel) {c u : ℝ} (hc : -1 / 2 < c)
    (hc' : c ≤ 1 / 2 + K.delta) (hu : 0 < u) : mellinInv c K.function u = K.transform u := by
  rw [transform, ← K.mellin_eq c u hc hc' hu]
  unfold mellinInv inverseMellin
  rw [Complex.real_smul]
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ (fun t ↦ by simp only [smul_eq_mul, mul_comm])

open MeasureTheory Set Filter in
open scoped Topology FourierTransform in
/-- A power identity used when transporting convergence through the exponential. -/
private theorem exp_mellin_weight (σ y : ℝ) (z : ℂ) :
    (Real.exp y : ℂ) * ((Real.exp y : ℂ) ^ ((σ : ℂ) - 1) * z) = (Real.exp (σ * y) : ℂ) * z := by
  rw [← mul_assoc]
  congr 1
  calc
    (Real.exp y : ℂ) * (Real.exp y : ℂ) ^ ((σ : ℂ) - 1) = (Real.exp y : ℂ) ^ (σ : ℂ) := by
      conv_lhs =>
        lhs; rw [← Complex.cpow_one (Real.exp y : ℂ)]
      rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero y))]
      congr 1
      ring
    _ = (Real.exp (σ * y) : ℂ) := by
      rw [← Complex.ofReal_cpow (Real.exp_pos y).le, Real.rpow_def_of_pos (Real.exp_pos y),
        Real.log_exp, mul_comm]

open MeasureTheory Set Filter in
open scoped Topology FourierTransform in
/-- Mellin convergence becomes ordinary integrability in logarithmic coordinates. -/
theorem integrable_logarithmic_transform (K : MellinKernel) {σ : ℝ} (hσ : 0 < σ)
    (hσ' : σ < 1 / 2 + K.delta) :
    Integrable (fun y : ℝ ↦ (Real.exp (-σ * y) : ℂ) * K.transform (Real.exp (-y))) := by
  have hm := mellinConvergent_transform K (s := (σ : ℂ)) hσ hσ'
  have he := (integrable_comp_exp (fun u : ℝ ↦ (u : ℂ) ^ ((σ : ℂ) - 1) * K.transform u)).mpr hm
  have hen := he.comp_neg
  apply hen.congr
  apply ae_of_all
  intro y
  change
    (Real.exp (-y) : ℂ) * ((Real.exp (-y) : ℂ) ^ ((σ : ℂ) - 1) * K.transform (Real.exp (-y))) = _
  simpa only [mul_neg, neg_mul] using exp_mellin_weight σ (-y) (K.transform (Real.exp (-y)))

open MeasureTheory Set Filter in
open scoped Topology FourierTransform in
/-- The Fourier inverse of a vertical kernel line is its Mellin inverse in
logarithmic coordinates, with the exact exponential weight. -/
theorem fourierInv_line_eq (K : MellinKernel) {σ : ℝ} (hσ : -1 / 2 < σ) (hσ' : σ ≤ 1 / 2 + K.delta)
    (y : ℝ) :
    𝓕⁻ (fun t : ℝ ↦ K.function ((σ : ℂ) + 2 * Real.pi * t * Complex.I)) y =
      (Real.exp (-σ * y) : ℂ) * K.transform (Real.exp (-y)) := by
  have hm := mellinInv_eq_transform K hσ hσ' (Real.exp_pos (-y))
  rw [mellinInv_eq_fourierInv σ K.function (Real.exp_pos (-y)), Real.log_exp, neg_neg] at hm
  have hp : (Real.exp (-y) : ℂ) ^ (-(σ : ℂ)) = (Real.exp (σ * y) : ℂ) := by
    rw [← Complex.ofReal_neg, ← Complex.ofReal_cpow (Real.exp_pos (-y)).le,
      Real.rpow_def_of_pos (Real.exp_pos (-y)), Real.log_exp]
    congr 2
    ring
  rw [hp, smul_eq_mul] at hm
  calc
    _ =
        (Real.exp (-σ * y) : ℂ) *
          ((Real.exp (σ * y) : ℂ) *
            𝓕⁻ (fun t : ℝ ↦ K.function ((σ : ℂ) + 2 * Real.pi * t * Complex.I)) y) :=
      by
      rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
      simp only [neg_mul, neg_add_cancel, Real.exp_zero, Complex.ofReal_one, one_mul]
    _ = _ := by rw [hm]

open MeasureTheory Set Filter in
open scoped Topology FourierTransform in
/-- General forward Mellin reconstruction at a positive real coordinate inside
the strip. The two-sided convergence needed by Fourier inversion is proved from
the admissible kernel's existing line bounds. -/
theorem mellin_transform_eq_function (K : MellinKernel) {σ : ℝ} (hσ : 0 < σ)
    (hσ' : σ < 1 / 2 + K.delta) : mellin K.transform (σ : ℂ) = K.function (σ : ℂ) := by
  let g : ℝ → ℂ := fun t ↦ K.function ((σ : ℂ) + 2 * Real.pi * t * Complex.I)
  have hlow : -1 / 2 < σ := by linarith only [hσ]
  have hg : Integrable g := by
    have hline :=
      (integrable_line K hlow hσ'.le).comp_mul_left'
        (show 2 * Real.pi ≠ 0 from (mul_pos (by norm_num only) Real.pi_pos).ne')
    convert hline using 1
    ext t
    dsimp only [g]
    congr 1
    simp only [Complex.ofReal_mul, Complex.ofReal_ofNat]
    ring
  have hginv : Integrable (𝓕⁻ g) := by
    have hh := integrable_logarithmic_transform K hσ hσ'
    apply hh.congr
    exact ae_of_all _ (fun y ↦ (fourierInv_line_eq K hlow hσ'.le y).symm)
  have hgfourier : Integrable (𝓕 g) := by
    have hh := hginv.comp_neg
    simpa only [Real.fourierInv_eq_fourier_neg, neg_neg] using hh
  have hgcont : ContinuousAt g 0 := by
    have hreg : (σ : ℂ) ∈ K.region :=
      K.strip_subset
        (by
          simp only [Set.mem_ofPred_eq, Complex.ofReal_re]
          constructor <;> linarith only [hσ, hσ', K.delta_pos])
    have hpole : (σ : ℂ) ≠ -1 / 2 := by
      intro he
      have hr := congrArg Complex.re he
      norm_num only [Complex.neg_re, Complex.div_ofNat_re, Complex.ofReal_re, Complex.one_re] at hr
      linarith only [hr, hσ]
    have hd :=
      K.holomorphic.differentiableAt
        ((K.region_open.sdiff isClosed_singleton).mem_nhds ⟨hreg, hpole⟩)
    have hout : ContinuousAt K.function ((σ : ℂ) + 2 * Real.pi * (0 : ℝ) * Complex.I) := by
      simpa only [Complex.ofReal_zero, mul_zero, zero_mul, add_zero] using hd.continuousAt
    exact hout.comp (f := fun t : ℝ ↦ (σ : ℂ) + 2 * Real.pi * t * Complex.I) (x := 0) (by fun_prop)
  have hinv := hg.fourier_fourierInv_eq hgfourier hgcont
  have he : (fun y : ℝ ↦ (Real.exp (-σ * y) : ℂ) * K.transform (Real.exp (-y))) = 𝓕⁻ g := by
    funext y
    exact (fourierInv_line_eq K hlow hσ'.le y).symm
  rw [mellin_eq_fourier]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_div, Complex.real_smul, he]
  simpa only [g, Complex.ofReal_zero, mul_zero, zero_mul, add_zero] using hinv

open MeasureTheory Set Filter in
open scoped Topology FourierTransform in
/-- At the central positive coordinate the complex Mellin weight has real part
equal to the weight used in Proposition 6.1. -/
theorem mellin_half_weight_re (K : MellinKernel) {u : ℝ} (hu : 0 < u) :
    (((u : ℂ) ^ ((1 / 2 : ℂ) - 1)) • K.transform u).re = (K.transform u).re / Real.sqrt u := by
  have hp : (u : ℂ) ^ ((1 / 2 : ℂ) - 1) = ((Real.sqrt u)⁻¹ : ℝ) := by
    calc
      (u : ℂ) ^ ((1 / 2 : ℂ) - 1) = ((u ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
        convert (Complex.ofReal_cpow hu.le (-(1 / 2 : ℝ))).symm using 1
        norm_num only [Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_one,
          Complex.ofReal_ofNat]
      _ = _ := by rw [Real.rpow_neg hu.le, ← Real.sqrt_eq_rpow]
  rw [smul_eq_mul, hp]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    div_eq_mul_inv, mul_comm]

open MeasureTheory Set Filter in
open scoped Topology FourierTransform in
/-- The whole positive-axis weight in Proposition 6.1 is integrable. -/
theorem integrableOn_weight_Ioi (K : MellinKernel) :
    IntegrableOn (fun u : ℝ ↦ (K.transform u).re / Real.sqrt u) (Ioi 0) := by
  have hm :=
    mellinConvergent_transform K (s := (1 / 2 : ℂ))
      (by norm_num only [Complex.div_ofNat_re, Complex.one_re])
      (by
        norm_num only [Complex.div_ofNat_re, Complex.one_re]
        linarith only [K.delta_pos])
  apply hm.re.congr
  exact (ae_restrict_mem measurableSet_Ioi).mono fun u hu ↦ mellin_half_weight_re K hu

open MeasureTheory Set Filter in
open scoped Topology FourierTransform in
/-- Forward Mellin reconstruction for the exact Proposition 6.1 weight. -/
theorem integral_weight_Ioi_eq (K : MellinKernel) :
    (∫ u : ℝ in Ioi 0, (K.transform u).re / Real.sqrt u) = (K.function (1 / 2)).re := by
  have hm :=
    mellinConvergent_transform K (s := (1 / 2 : ℂ))
      (by norm_num only [Complex.div_ofNat_re, Complex.one_re])
      (by
        norm_num only [Complex.div_ofNat_re, Complex.one_re]
        linarith only [K.delta_pos])
  have hv :=
    mellin_transform_eq_function K (σ := (1 / 2 : ℝ))
      (by norm_num only [Complex.div_ofNat_re, Complex.one_re])
      (by
        norm_num only [Complex.div_ofNat_re, Complex.one_re]
        linarith only [K.delta_pos])
  have hr := congrArg Complex.re hv
  norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at hr
  rw [← hr]
  unfold mellin
  have hri := integral_re hm
  simp only [RCLike.re_eq_complex_re] at hri
  rw [← hri]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  exact (mellin_half_weight_re K hu).symm

end PseudoPrime.LLS.PaperStatements.MellinKernel
