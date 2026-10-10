/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.MethodBarrier.IndexSixNumerics
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Tactic.FieldSimp

/-! # The integrable dual weight for the index-six obstruction

The dual weight is a linear combination of two left half-line exponentials.
This makes its integrability and Fourier transform direct consequences of
the existing complex exponential integral. The values at the two endpoints
are chosen to match `Iic`, and do not affect any Lebesgue integral.

The Fourier pairing identity is the existing bilinear Fubini theorem in
mathlib. Its norm bound therefore applies to every complex integrable test
function, without a sign condition on the real part of its Fourier transform.
-/

@[expose] public section

namespace PseudoPrime.LLS.IndexSixBarrier

open MeasureTheory in
open scoped FourierTransform RealInnerProductSpace in
/-- The positive endpoint of the truncated dual penalty. -/
noncomputable def cutoff : ℝ :=
  shift / Real.pi

open MeasureTheory in
open scoped FourierTransform RealInnerProductSpace in
/-- The dual cutoff is positive because the logarithmic shift and pi are positive. -/
theorem cutoff_pos : 0 < cutoff :=
  div_pos shift_pos Real.pi_pos

open MeasureTheory in
open scoped FourierTransform RealInnerProductSpace in
/-- A left half-line exponential used to express the dual weight. -/
noncomputable def leftExponential (a t : ℝ) : ℝ :=
  (Set.Iic a).indicator (fun u : ℝ ↦ Real.exp (Real.pi * u)) t

open MeasureTheory in
open scoped FourierTransform RealInnerProductSpace in
/-- The real dual weight. Away from the two endpoints, it is
`exp(pi*t)` on the negative half-line, `-exp(pi*t)/5` on `(0,cutoff)`,
and zero beyond the cutoff. -/
noncomputable def dualWeight (t : ℝ) : ℝ :=
  (6 / 5 : ℝ) * leftExponential 0 t - (1 / 5 : ℝ) * leftExponential cutoff t

open MeasureTheory in
open scoped FourierTransform RealInnerProductSpace in
/-- The dual weight vanishes at nonpositive arguments by its support condition. -/
theorem dualWeight_of_nonpos {t : ℝ} (ht : t ≤ 0) : dualWeight t = Real.exp (Real.pi * t) := by
  have htc : t ≤ cutoff := ht.trans cutoff_pos.le
  have ht0 : t ∈ Set.Iic (0 : ℝ) := by simpa only [Set.mem_Iic] using! ht
  have htcut : t ∈ Set.Iic cutoff := by simpa only [Set.mem_Iic] using! htc
  simp only [dualWeight, leftExponential, Set.indicator_of_mem ht0, Set.indicator_of_mem htcut]
  ring

open MeasureTheory in
open scoped FourierTransform RealInnerProductSpace in
/-- On its positive support the dual weight equals exp(pi*t)/5. -/
theorem dualWeight_of_pos_le {t : ℝ} (ht : 0 < t) (htc : t ≤ cutoff) :
    dualWeight t = -(1 / 5 : ℝ) * Real.exp (Real.pi * t) := by
  have ht0 : t ∉ Set.Iic (0 : ℝ) := by simpa only [Set.mem_Iic] using! (not_le_of_gt ht)
  have htcut : t ∈ Set.Iic cutoff := by simpa only [Set.mem_Iic] using! htc
  simp only [dualWeight, leftExponential, Set.indicator_of_notMem ht0, Set.indicator_of_mem htcut,
    mul_zero, zero_sub, neg_mul]

open MeasureTheory in
open scoped FourierTransform RealInnerProductSpace in
/-- The dual weight vanishes beyond the cutoff, giving compact support. -/
theorem dualWeight_of_cutoff_lt {t : ℝ} (htc : cutoff < t) : dualWeight t = 0 := by
  have ht : 0 < t := cutoff_pos.trans htc
  have ht0 : t ∉ Set.Iic (0 : ℝ) := by simpa only [Set.mem_Iic] using! (not_le_of_gt ht)
  have htcut : t ∉ Set.Iic cutoff := by simpa only [Set.mem_Iic] using! (not_le_of_gt htc)
  simp only [dualWeight, leftExponential, Set.indicator_of_notMem ht0,
    Set.indicator_of_notMem htcut, mul_zero, sub_self]

open MeasureTheory in
open scoped FourierTransform RealInnerProductSpace in
private theorem integrable_leftExponential (a : ℝ) : Integrable (leftExponential a) :=
  (integrableOn_exp_mul_Iic Real.pi_pos a).integrable_indicator measurableSet_Iic

open MeasureTheory in
open scoped FourierTransform RealInnerProductSpace in
/-- The dual weight is integrable on the whole real line. -/
theorem integrable_dualWeight : Integrable dualWeight :=
  ((integrable_leftExponential 0).const_mul (6 / 5 : ℝ)).sub
    ((integrable_leftExponential cutoff).const_mul (1 / 5 : ℝ))

open MeasureTheory in
open scoped FourierTransform RealInnerProductSpace in
private theorem continuous_fourier_of_integrable {F : ℝ → ℂ} (hF : Integrable F) :
    Continuous (FourierTransform.fourier F) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner hF

open MeasureTheory in
open scoped FourierTransform RealInnerProductSpace in
private theorem norm_fourier_le (F : ℝ → ℂ) (x : ℝ) :
    ‖FourierTransform.fourier F x‖ ≤ ∫ t : ℝ, ‖F t‖ :=
  VectorFourier.norm_fourierIntegral_le_integral_norm Real.fourierChar volume (innerₗ ℝ) F x

open MeasureTheory in
open scoped FourierTransform RealInnerProductSpace in
/-- The real Fourier pairing with the dual weight is absolutely integrable. -/
theorem integrable_dual_pairing (F : ℝ → ℂ) (hF : Integrable F) :
    Integrable (fun t : ℝ ↦ dualWeight t * (FourierTransform.fourier F t).re) := by
  apply
    integrable_dualWeight.mul_bdd
      (Complex.continuous_re.comp (continuous_fourier_of_integrable hF)).aestronglyMeasurable
  exact
    ae_of_all _
      (fun t ↦ by
        simpa only [Real.norm_eq_abs, Function.comp_apply] using!
          (Complex.abs_re_le_norm (FourierTransform.fourier F t)).trans (norm_fourier_le F t))

open MeasureTheory in
open scoped FourierTransform RealInnerProductSpace in
private theorem integrable_dual_complex_pairing (F : ℝ → ℂ) (hF : Integrable F) :
    Integrable (fun t : ℝ ↦ (dualWeight t : ℂ) * FourierTransform.fourier F t) := by
  simpa only using!
    (integrable_dualWeight.ofReal : Integrable (fun t : ℝ ↦ (dualWeight t : ℂ))).mul_bdd
      (continuous_fourier_of_integrable hF).aestronglyMeasurable
      (ae_of_all volume (norm_fourier_le F))

open MeasureTheory in
open scoped FourierTransform RealInnerProductSpace in
private theorem fourier_linear_combination (F G : ℝ → ℂ) (hF : Integrable F) (hG : Integrable G)
    (a b : ℂ) (x : ℝ) :
    FourierTransform.fourier (fun t ↦ a * F t - b * G t) x =
      a * FourierTransform.fourier F x - b * FourierTransform.fourier G x := by
  have hiF := (Real.fourierIntegral_convergent_iff x).2 hF
  have hiG := (Real.fourierIntegral_convergent_iff x).2 hG
  rw [Real.fourier_eq, Real.fourier_eq, Real.fourier_eq]
  calc
    (∫ t : ℝ, Real.fourierChar (-inner ℝ t x) • (a * F t - b * G t)) =
        ∫ t : ℝ,
          a * (Real.fourierChar (-inner ℝ t x) • F t) -
            b * (Real.fourierChar (-inner ℝ t x) • G t) :=
      by
      apply integral_congr_ae
      exact
        ae_of_all _
          (fun t ↦ by
            simp only [Circle.smul_def, smul_eq_mul]
            ring)
    _ = _ := by
      rw [integral_sub (hiF.const_mul a) (hiG.const_mul b), integral_const_mul, integral_const_mul]

open MeasureTheory in
open scoped FourierTransform RealInnerProductSpace in
private theorem fourier_leftExponential (a x : ℝ) :
    FourierTransform.fourier (fun t : ℝ ↦ (leftExponential a t : ℂ)) x =
      Complex.exp (((Real.pi : ℂ) * (1 - 2 * Complex.I * (x : ℂ))) * (a : ℂ)) /
        ((Real.pi : ℂ) * (1 - 2 * Complex.I * (x : ℂ))) := by
  let z : ℂ := (Real.pi : ℂ) * (1 - 2 * Complex.I * (x : ℂ))
  have hz : 0 < z.re := by
    simpa only [z, Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.re_ofNat,
      Complex.im_ofNat, mul_zero, zero_mul, sub_zero, add_zero, zero_add, mul_one] using Real.pi_pos
  have hi (t : ℝ) :
    Complex.exp ((↑(-2 * Real.pi * inner ℝ t x) : ℂ) * Complex.I) • (leftExponential a t : ℂ) =
      (Set.Iic a).indicator (fun u : ℝ ↦ Complex.exp (z * (u : ℂ))) t := by
    by_cases ht : t ≤ a
    · have htm : t ∈ Set.Iic a := by simpa only [Set.mem_Iic] using! ht
      simp only [leftExponential, Set.indicator_of_mem htm, smul_eq_mul, Complex.ofReal_exp,
        ← Complex.exp_add]
      congr 1
      simp only [z, Real.inner_apply, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_ofNat]
      ring
    · have htm : t ∉ Set.Iic a := by simpa only [Set.mem_Iic] using! ht
      simp only [leftExponential, Set.indicator_of_notMem htm, Complex.ofReal_zero, smul_zero]
  calc
    FourierTransform.fourier (fun t : ℝ ↦ (leftExponential a t : ℂ)) x =
        ∫ t : ℝ, (Set.Iic a).indicator (fun u : ℝ ↦ Complex.exp (z * (u : ℂ))) t :=
      by
      rw [Real.fourier_eq']
      exact integral_congr_ae (ae_of_all _ hi)
    _ = ∫ t : ℝ in Set.Iic a, Complex.exp (z * (t : ℂ)) := integral_indicator measurableSet_Iic
    _ = _ := integral_exp_mul_complex_Iic hz a

open MeasureTheory in
open scoped FourierTransform RealInnerProductSpace in
/-- The exact Fourier transform of the integrable dual weight, normalized
to the complex function whose global norm bound is certified separately. -/
theorem fourier_dualWeight (x : ℝ) :
    FourierTransform.fourier (fun t : ℝ ↦ (dualWeight t : ℂ)) x =
      dualValue (2 * x) / (2 * Real.pi : ℂ) := by
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hden : (1 - 2 * Complex.I * (x : ℂ)) ≠ 0 := by
    intro he
    have hr := congrArg Complex.re he
    norm_num only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.re_ofNat, Complex.im_ofNat,
      Complex.mul_im, Complex.zero_re, zero_mul, mul_zero, sub_zero] at hr
  have hexp : Real.exp shift = (5 / 2 : ℝ) := by
    exact Real.exp_log (by norm_num only : (0 : ℝ) < 5 / 2)
  have hm :
    ((Real.pi : ℂ) * (1 - 2 * Complex.I * (x : ℂ))) * (cutoff : ℂ) =
      (shift : ℂ) + (-Complex.I * (shift : ℂ) * ((2 * x : ℝ) : ℂ)) := by
    simp only [cutoff, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_ofNat]
    field_simp (disch :=
      first
      | exact hp
      | norm_num only)
    ring
  have he :
    Complex.exp (((Real.pi : ℂ) * (1 - 2 * Complex.I * (x : ℂ))) * (cutoff : ℂ)) =
      (5 / 2 : ℂ) * Complex.exp (-Complex.I * (shift : ℂ) * ((2 * x : ℝ) : ℂ)) := by
    rw [hm, Complex.exp_add, ← Complex.ofReal_exp, hexp]
    norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat]
  have hw :
    (fun t : ℝ ↦ (dualWeight t : ℂ)) = fun t : ℝ ↦
      (6 / 5 : ℂ) * (leftExponential 0 t : ℂ) - (1 / 5 : ℂ) * (leftExponential cutoff t : ℂ) := by
    funext t
    simp only [dualWeight, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_div,
      Complex.ofReal_one, Complex.ofReal_ofNat]
  have hlin :
    FourierTransform.fourier
        (fun t : ℝ ↦
          (6 / 5 : ℂ) * (leftExponential 0 t : ℂ) - (1 / 5 : ℂ) * (leftExponential cutoff t : ℂ))
        x =
      (6 / 5 : ℂ) * FourierTransform.fourier (fun t : ℝ ↦ (leftExponential 0 t : ℂ)) x -
        (1 / 5 : ℂ) * FourierTransform.fourier (fun t : ℝ ↦ (leftExponential cutoff t : ℂ)) x := by
    simpa only using!
      fourier_linear_combination _ _ (integrable_leftExponential 0).ofReal
        (integrable_leftExponential cutoff).ofReal (6 / 5 : ℂ) (1 / 5 : ℂ) x
  rw [hw, hlin, fourier_leftExponential, fourier_leftExponential, Complex.ofReal_zero, mul_zero,
    Complex.exp_zero, he]
  simp only [dualValue, Complex.ofReal_mul, Complex.ofReal_ofNat]
  have hden' : (1 - Complex.I * (2 * (x : ℂ))) ≠ 0 := by
    convert hden using 1
    ring
  field_simp (disch :=
    first
    | exact hp
    | exact hden
    | exact hden'
    | norm_num only)

open MeasureTheory in
open scoped FourierTransform RealInnerProductSpace in
/-- Bilinear Fourier Fubini, specialized to the real dual weight. -/
theorem integral_dualWeight_fourier (F : ℝ → ℂ) (hF : Integrable F) :
    (∫ t : ℝ, (dualWeight t : ℂ) * FourierTransform.fourier F t) =
      ∫ x : ℝ, F x * FourierTransform.fourier (fun t : ℝ ↦ (dualWeight t : ℂ)) x := by
  have hs :=
    VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ) Real.continuous_fourierChar
      continuous_inner hF
      (integrable_dualWeight.ofReal : Integrable (fun t : ℝ ↦ (dualWeight t : ℂ)))
  simpa only [flip_innerₗ, smul_eq_mul, mul_comm, FourierTransform.fourier] using! hs

open MeasureTheory in
open scoped FourierTransform RealInnerProductSpace in
private theorem fourier_dualWeight_norm_le (x : ℝ) :
    ‖FourierTransform.fourier (fun t : ℝ ↦ (dualWeight t : ℂ)) x‖ ≤
      Real.sqrt (121 / 60 : ℝ) / (2 * Real.pi) := by
  have hb : ‖dualValue (2 * x)‖ ≤ Real.sqrt (121 / 60 : ℝ) :=
    Real.le_sqrt_of_sq_le (dualValue_norm_sq_le (2 * x))
  rw [fourier_dualWeight, norm_div]
  have hp : ‖(2 * Real.pi : ℂ)‖ = 2 * Real.pi := by
    rw [show (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by
        simp only [Complex.ofReal_mul, Complex.ofReal_ofNat],
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (mul_pos (by norm_num only) Real.pi_pos)]
  rw [hp]
  exact div_le_div_of_nonneg_right hb (mul_pos (by norm_num only) Real.pi_pos).le

open MeasureTheory in
open scoped FourierTransform RealInnerProductSpace in
/-- The dual pairing is bounded by the global Fourier norm times the L1 norm.
No sign or reality assumption on the Fourier transform of `F` is required. -/
theorem dual_pairing_le (F : ℝ → ℂ) (hF : Integrable F) :
    2 * Real.pi * (∫ t : ℝ, dualWeight t * (FourierTransform.fourier F t).re) ≤
      Real.sqrt (121 / 60 : ℝ) * (∫ x : ℝ, ‖F x‖) := by
  have hre :
    (∫ t : ℝ, dualWeight t * (FourierTransform.fourier F t).re) =
      (∫ t : ℝ, (dualWeight t : ℂ) * FourierTransform.fourier F t).re := by
    simpa only [RCLike.re_to_complex, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero] using! (integral_re (integrable_dual_complex_pairing F hF))
  have hn :
    ‖∫ x : ℝ, F x * FourierTransform.fourier (fun t : ℝ ↦ (dualWeight t : ℂ)) x‖ ≤
      (Real.sqrt (121 / 60 : ℝ) / (2 * Real.pi)) * (∫ x : ℝ, ‖F x‖) := by
    have hb :=
      norm_integral_le_of_norm_le (f := fun x : ℝ ↦
        F x * FourierTransform.fourier (fun t : ℝ ↦ (dualWeight t : ℂ)) x)
        (hF.norm.const_mul (Real.sqrt (121 / 60 : ℝ) / (2 * Real.pi)))
        (ae_of_all volume
          (fun x ↦ by
            rw [norm_mul]
            exact
              (mul_le_mul_of_nonneg_left (fourier_dualWeight_norm_le x)
                    (norm_nonneg (F x))).trans_eq
                (mul_comm _ _)))
    simpa only [integral_const_mul] using hb
  have hh :
    (∫ t : ℝ, dualWeight t * (FourierTransform.fourier F t).re) ≤
      (Real.sqrt (121 / 60 : ℝ) / (2 * Real.pi)) * (∫ x : ℝ, ‖F x‖) := by
    rw [hre, integral_dualWeight_fourier F hF]
    exact (Complex.re_le_norm _).trans hn
  have hp : 0 < 2 * Real.pi := mul_pos (by norm_num only) Real.pi_pos
  have hb := mul_le_mul_of_nonneg_left hh hp.le
  calc
    _ ≤ 2 * Real.pi * ((Real.sqrt (121 / 60 : ℝ) / (2 * Real.pi)) * (∫ x : ℝ, ‖F x‖)) := hb
    _ = _ := by
      field_simp (disch :=
        first
        | exact Real.pi_ne_zero
        | norm_num only)

end PseudoPrime.LLS.IndexSixBarrier
