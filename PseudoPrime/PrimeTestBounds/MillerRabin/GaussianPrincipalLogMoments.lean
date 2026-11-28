/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighPrincipalError
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianLaplaceMoment
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Ring

/-! # Logarithmic coordinates of the principal remainder moments -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Negated logarithm maps the interval below the reciprocal cutoff to the log tail. -/
private theorem neg_log_image_low {X : ℝ} (hX : 0 < X) :
    (fun u : ℝ ↦ -Real.log u) '' Set.Ioo 0 X⁻¹ = Set.Ioi (Real.log X) := by
  ext t
  constructor
  · rintro ⟨u, hu, rfl⟩
    have h := Real.log_lt_log hu.1 hu.2
    rw [Real.log_inv] at h
    apply Set.mem_Ioi.mpr
    simpa only [neg_neg] using neg_lt_neg h
  · intro ht
    refine ⟨Real.exp (-t), ⟨Real.exp_pos _, ?_⟩, ?_⟩
    · rw [← Real.exp_log (inv_pos.mpr hX), Real.log_inv]
      exact Real.exp_lt_exp.mpr (neg_lt_neg ht)
    · change -Real.log (Real.exp (-t)) = t
      rw [Real.log_exp, neg_neg]

/-- The small-argument remainder moment becomes the exponential tail of the absolute
derivative polynomial. This is the first integral in H27 before translation. -/
public theorem reflected_low_abs_moment (D : Polynomial ℝ) (d b : ℝ) {X : ℝ} (hX : 0 < X) :
    (∫ u in (0 : ℝ)..X⁻¹, u ^ (d - 1) * |D.eval (b - Real.log u)|) =
      ∫ t in Set.Ioi (Real.log X), Real.exp (-d * t) * |D.eval (b + t)| := by
  let g := fun t : ℝ ↦ Real.exp (-d * t) * |D.eval (b + t)|
  have hd (u : ℝ) (hu : u ∈ Set.Ioo 0 X⁻¹) :
    HasDerivWithinAt (fun v : ℝ ↦ -Real.log v) (-u⁻¹) (Set.Ioo 0 X⁻¹) u :=
    (Real.hasDerivAt_log hu.1.ne').neg.hasDerivWithinAt
  have hi : Set.InjOn (fun u : ℝ ↦ -Real.log u) (Set.Ioo 0 X⁻¹) := fun _ hu _ hv he ↦
    Real.log_injOn_pos hu.1 hv.1 (neg_injective he)
  have h := MeasureTheory.integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hd hi g
  rw [neg_log_image_low hX] at h
  rw [intervalIntegral.integral_of_le (inv_pos.mpr hX).le,
    MeasureTheory.integral_Ioc_eq_integral_Ioo, h]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
  intro u hu
  have hp : 0 < u := hu.1
  simp only [g, abs_neg, abs_of_nonneg (inv_pos.mpr hp).le, smul_eq_mul, sub_eq_add_neg]
  rw [show -d * -Real.log u = Real.log u * d by ring, ← Real.rpow_def_of_pos hp, ← mul_assoc, ←
    Real.rpow_neg_one, ← Real.rpow_add hp]
  congr 2
  ring

/-- The reflected logarithm carries the large-argument domain to a bounded interval. -/
private theorem reflect_log_image {X b : ℝ} (hX : 0 < X) :
    (fun u : ℝ ↦ b - Real.log u) '' Set.Ioo X⁻¹ (Real.exp b) = Set.Ioo 0 (b + Real.log X) := by
  ext t
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hp := (inv_pos.mpr hX).trans hu.1
    have h₁ := Real.log_lt_log hp hu.2
    have h₂ := Real.log_lt_log (inv_pos.mpr hX) hu.1
    rw [Real.log_exp] at h₁
    rw [Real.log_inv] at h₂
    exact ⟨sub_pos.mpr h₁, (sub_lt_sub_left h₂ b).trans_eq (sub_neg_eq_add _ _)⟩
  · intro ht
    refine ⟨Real.exp (b - t), ⟨?_, ?_⟩, ?_⟩
    · rw [← Real.exp_log (inv_pos.mpr hX), Real.log_inv]
      exact Real.exp_lt_exp.mpr (neg_lt_sub_iff_lt_add.mpr ((add_comm b (Real.log X)) ▸ ht.2))
    · exact Real.exp_lt_exp.mpr (sub_lt_self b ht.1)
    · change b - Real.log (Real.exp (b - t)) = t
      rw [Real.log_exp, sub_sub_cancel]

/-- The large-argument moment in H27 remains an integral over a finite interval.
This substitution only requires positive endpoints and imposes no upper bound on `d`. -/
public theorem reflected_high_abs_moment (D : Polynomial ℝ) (d b : ℝ) {X : ℝ} (hX : 0 < X)
    (hcut : X⁻¹ ≤ Real.exp b) :
    (∫ u in X⁻¹..Real.exp b, u⁻¹ ^ 2 * (u ^ (d - 1) * |D.eval (b - Real.log u)|)) =
      Real.exp ((d - 2) * b) *
        ∫ t in (0 : ℝ)..(b + Real.log X), Real.exp (-(d - 2) * t) * |D.eval t| := by
  let g := fun t : ℝ ↦ Real.exp ((d - 2) * (b - t)) * |D.eval t|
  have hd (u : ℝ) (hu : u ∈ Set.Ioo X⁻¹ (Real.exp b)) :
    HasDerivWithinAt (fun v : ℝ ↦ b - Real.log v) (-u⁻¹) (Set.Ioo X⁻¹ (Real.exp b)) u := by
    change HasDerivWithinAt ((fun _ : ℝ ↦ b) - Real.log) (-u⁻¹) _ u
    simpa only [zero_sub] using
      ((hasDerivAt_const u b).sub
          (Real.hasDerivAt_log ((inv_pos.mpr hX).trans hu.1).ne')).hasDerivWithinAt
  have hi : Set.InjOn (fun u : ℝ ↦ b - Real.log u) (Set.Ioo X⁻¹ (Real.exp b)) := fun _ hu _ hv he ↦
    Real.log_injOn_pos ((inv_pos.mpr hX).trans hu.1) ((inv_pos.mpr hX).trans hv.1)
      (sub_right_injective he)
  have hj := MeasureTheory.integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hd hi g
  rw [reflect_log_image hX] at hj
  have htop : 0 ≤ b + Real.log X := by
    have h := Real.log_le_log (inv_pos.mpr hX) hcut
    rw [Real.log_inv, Real.log_exp] at h
    exact neg_le_iff_add_nonneg.mp h
  rw [← intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le htop,
    MeasureTheory.integral_Ioc_eq_integral_Ioo, intervalIntegral.integral_of_le hcut,
    MeasureTheory.integral_Ioc_eq_integral_Ioo]
  calc
    _ = ∫ u in Set.Ioo X⁻¹ (Real.exp b), |-u⁻¹| • g (b - Real.log u) := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
      intro u hu
      have hp := (inv_pos.mpr hX).trans hu.1
      simp only [g, abs_neg, abs_of_nonneg (inv_pos.mpr hp).le, smul_eq_mul, sub_sub_cancel]
      have he : u⁻¹ ^ (2 : ℕ) = u ^ (-2 : ℝ) := by
        rw [← Real.rpow_two, ← Real.rpow_neg_one, ← Real.rpow_mul hp.le]
        norm_num only
      rw [mul_comm (d - 2) (Real.log u), ← Real.rpow_def_of_pos hp, ← mul_assoc, ← mul_assoc, he, ←
        Real.rpow_neg_one, ← Real.rpow_add hp, ← Real.rpow_add hp]
      congr 2
      ring
    _ = ∫ t in Set.Ioo 0 (b + Real.log X), g t := hj.symm
    _ = _ := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
      intro t _
      dsimp only [g]
      rw [mul_sub, sub_eq_add_neg, Real.exp_add, neg_mul, mul_assoc]

/-- Logarithmic-coordinate form of the high Gaussian principal remainder bound.
The large-argument term retains the finite exponential moment in H27. -/
public theorem high_principal_log_moments (K : HighGaussianKernel) (hRH : RiemannHypothesis) {X : ℝ}
    (hX : 1 ≤ X) :
    let d := (K.pole : ℝ) - 1 / 2
    let B := K.realProfile
    let D :=
      Polynomial.C (d ^ 2) * B - Polynomial.C (2 * d) * B.derivative + B.derivative.derivative
    let W := fun u : ℝ ↦ u ^ d * B.eval (5 - Real.log u)
    let F := fun u : ℝ ↦ u * deriv W u
    let Q := deriv F
    |principalErrorFunctional Q gaussianLogZetaError (F 1) X (Real.exp 5) -
          principalErrorFunctional Q gaussianLogZetaZeroSum (F 1) X (Real.exp 5)| ≤
      51 / 10 * (∫ t in Set.Ioi (Real.log X), Real.exp (-d * t) * |D.eval (5 + t)|) +
        5 / 4 * X⁻¹ ^ 2 * Real.exp ((d - 2) * 5) *
          (∫ t in (0 : ℝ)..(5 + Real.log X), Real.exp (-(d - 2) * t) * |D.eval t|) +
        5 / 3 * |F 1| * X⁻¹ ^ 2 := by
  intro d B D W F Q
  have hX₀ := zero_lt_one.trans_le hX
  have hy : X⁻¹ ≤ Real.exp 5 :=
    ((inv_le_one₀ hX₀).mpr hX).trans (Real.one_le_exp_iff.mpr (by norm_num only))
  have hq (u : ℝ) (hu : 0 < u) : |Q u| = u ^ (d - 1) * |D.eval (5 - Real.log u)| := by
    change |deriv F u| = _
    rw [show deriv F u = _ from (reflected_log_weight_second B d 5 hu).deriv, abs_mul,
      abs_of_nonneg (Real.rpow_nonneg hu.le _)]
  have h₁ :
    (∫ u in (0 : ℝ)..X⁻¹, |Q u|) =
      ∫ t in Set.Ioi (Real.log X), Real.exp (-d * t) * |D.eval (5 + t)| :=
    (intervalIntegral.integral_congr_Ioo_of_le (inv_pos.mpr hX₀).le (fun u hu ↦ hq u hu.1)).trans
      (reflected_low_abs_moment D d 5 hX₀)
  have h₂ :
    (∫ u in X⁻¹..Real.exp 5, u⁻¹ ^ 2 * |Q u|) =
      Real.exp ((d - 2) * 5) *
        ∫ t in (0 : ℝ)..(5 + Real.log X), Real.exp (-(d - 2) * t) * |D.eval t| :=
    (intervalIntegral.integral_congr_Ioo_of_le hy
          (fun u hu ↦ congrArg (u⁻¹ ^ 2 * ·) (hq u ((inv_pos.mpr hX₀).trans hu.1)))).trans
      (reflected_high_abs_moment D d 5 hX₀ hy)
  have h := high_principal_error_remainder K hRH hX
  change
    _ ≤
      51 / 10 * (∫ u in (0 : ℝ)..X⁻¹, |Q u|) +
        5 / 4 * X⁻¹ ^ 2 * (∫ u in X⁻¹..Real.exp 5, u⁻¹ ^ 2 * |Q u|) +
        5 / 3 * |F 1| * X⁻¹ ^ 2 at h
  rw [h₁, h₂] at h
  simpa only [mul_assoc] using h

/-- Translating the lower-tail moment extracts the exponential at the logarithmic cutoff. -/
private theorem translated_reflected_abs_moment (D : Polynomial ℝ) (d b z : ℝ) :
    (∫ t in Set.Ioi z, Real.exp (-d * t) * |D.eval (b + t)|) =
      Real.exp (-d * z) * ∫ t in Set.Ioi (0 : ℝ), Real.exp (-d * t) * |D.eval (b + z + t)| := by
  rw [← integral_translate_Ioi (fun t ↦ Real.exp (-d * t) * |D.eval (b + t)|) z]
  have h (t : ℝ) :
    Real.exp (-d * (z + t)) * |D.eval (b + (z + t))| =
      Real.exp (-d * z) * (Real.exp (-d * t) * |D.eval (b + z + t)|) := by
    rw [mul_add, Real.exp_add, ← add_assoc, mul_assoc]
  simp only [h, MeasureTheory.integral_const_mul]

/-- Dividing the first H27 coefficient by `sqrt X` adds one half to its decay rate. -/
private theorem normalized_exp_decay {X : ℝ} (hX : 0 < X) (d : ℝ) :
    Real.exp (-d * Real.log X) / Real.sqrt X = Real.exp (-(d + 1 / 2) * Real.log X) := by
  rw [mul_comm (-d), ← Real.rpow_def_of_pos hX, Real.sqrt_eq_rpow, ← Real.rpow_sub hX,
    Real.rpow_def_of_pos hX]
  congr 1
  ring

/-- The inverse-square remainder coefficient decays at rate five halves after normalization. -/
private theorem normalized_inv_sq {X : ℝ} (hX : 0 < X) :
    X⁻¹ ^ (2 : ℕ) / Real.sqrt X = Real.exp (-(5 / 2 : ℝ) * Real.log X) := by
  rw [inv_pow, ← Real.rpow_two, ← Real.rpow_neg hX.le, Real.rpow_def_of_pos hX]
  rw [mul_comm (Real.log X), normalized_exp_decay hX]
  norm_num only

/-- H27 for either high Gaussian kernel, normalized by `sqrt X`.
The coefficient `exp ((d - 2) * 5)` stays outside the finite absolute moment. -/
public theorem high_principal_rem_normalized (K : HighGaussianKernel) (hRH : RiemannHypothesis)
    {X : ℝ} (hX : 1 ≤ X) :
    let d := (K.pole : ℝ) - 1 / 2
    let B := K.realProfile
    let D :=
      Polynomial.C (d ^ 2) * B - Polynomial.C (2 * d) * B.derivative + B.derivative.derivative
    let W := fun u : ℝ ↦ u ^ d * B.eval (5 - Real.log u)
    let F := fun u : ℝ ↦ u * deriv W u
    let Q := deriv F
    let z := Real.log X
    |principalErrorFunctional Q gaussianLogZetaError (F 1) X (Real.exp 5) -
            principalErrorFunctional Q gaussianLogZetaZeroSum (F 1) X (Real.exp 5)| /
        Real.sqrt X ≤
      51 / 10 * Real.exp (-(d + 1 / 2) * z) *
          (∫ t in Set.Ioi (0 : ℝ), Real.exp (-d * t) * |D.eval (5 + z + t)|) +
        5 / 4 * Real.exp (-(5 / 2 : ℝ) * z) * Real.exp ((d - 2) * 5) *
          (∫ t in (0 : ℝ)..(5 + z), Real.exp (-(d - 2) * t) * |D.eval t|) +
        5 / 3 * |F 1| * Real.exp (-(5 / 2 : ℝ) * z) := by
  intro d B D W F Q z
  have hX₀ := zero_lt_one.trans_le hX
  have h := div_le_div_of_nonneg_right (high_principal_log_moments K hRH hX) (Real.sqrt_nonneg X)
  have hs := normalized_exp_decay hX₀ d
  have hl := normalized_inv_sq hX₀
  dsimp only at h
  change
    _ / _ ≤
      (51 / 10 * (∫ t in Set.Ioi z, Real.exp (-d * t) * |D.eval (5 + t)|) +
          5 / 4 * X⁻¹ ^ 2 * Real.exp ((d - 2) * 5) *
            (∫ t in (0 : ℝ)..(5 + z), Real.exp (-(d - 2) * t) * |D.eval t|) +
          5 / 3 * |F 1| * X⁻¹ ^ 2) /
        Real.sqrt X at h
  rw [translated_reflected_abs_moment, add_div, add_div] at h
  refine h.trans_eq ?_
  rw [← hs, ← hl]
  ring

/-- Bound a finite absolute moment, including a nonpositive rate, by a complete
moment at a positive rate and one exponential factor at the endpoint. -/
public theorem finite_abs_moment_le_laplace (D : Polynomial ℝ) {r s z : ℝ} (hs : 0 < s)
    (hz : 0 ≤ z) :
    (∫ t in (0 : ℝ)..z, Real.exp (-r * t) * |D.eval t|) ≤
      Real.exp (max 0 (s - r) * z) *
        ∑ j ∈ Finset.range (D.natDegree + 1), |D.coeff j| * ((j.factorial : ℝ) / s ^ (j + 1)) := by
  have hc (a : ℝ) : Continuous (fun t : ℝ ↦ Real.exp (-a * t) * |D.eval t|) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul D.continuous.abs
  have h (t : ℝ) (ht : t ∈ Set.Icc 0 z) :
    Real.exp (-r * t) * |D.eval t| ≤
      Real.exp (max 0 (s - r) * z) * (Real.exp (-s * t) * |D.eval t|) := by
    have he : (s - r) * t ≤ max 0 (s - r) * z :=
      (mul_le_mul_of_nonneg_right (le_max_right _ _) ht.1).trans
        (mul_le_mul_of_nonneg_left ht.2 (le_max_left _ _))
    rw [← mul_assoc, ← Real.exp_add]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith only [he])) (abs_nonneg _)
  have hi :=
    intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hz ((hc r).intervalIntegrable 0 z)
      (((hc s).const_mul _).intervalIntegrable 0 z) h
  rw [intervalIntegral.integral_const_mul] at hi
  exact
    hi.trans
      (mul_le_mul_of_nonneg_left (polynomial_abs_laplace_interval_le D hs hz) (Real.exp_nonneg _))

end PseudoPrime.PrimeTestBounds.MillerRabin
