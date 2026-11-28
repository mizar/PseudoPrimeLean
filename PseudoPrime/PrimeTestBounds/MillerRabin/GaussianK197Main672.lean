/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Main572
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Main426
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Main354
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK137Later
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197ReflectionEarly
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197ReflectCredit
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterGammaEndpoints656
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197ConductorTail
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPrincipalTail663
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterReflectBox663
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterAuxReflectTail656
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Profile
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Conductor

/-! # Principal and reflected bounds for K197 through radius 672 -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For radii from 332.15 to 672, the combined K197 reflection
is at least -0.000491 by the common endpoint moment estimate. -/
theorem gaussian_joint_to672 (hRH : RiemannHypothesis) {r : ℝ} (hr : r ∈ Set.Icc 332.15 672)
    (α : ℕ → ℝ) (hα : ∀ n, 0 ≤ α n ∧ α n ≤ 4)
    (hprefix : ∀ n : ℕ, (n : ℝ) ≤ r ^ 2 → ArithmeticFunction.vonMangoldt n ≠ 0 → α n = 0) :
    (-0.000491 : ℝ) ≤
      ∑ i, (gaussianCoeff197 i : ℝ) * quarterAuxReflection656 α r (quarterShift663 i : ℝ) := by
  have hhi :=
    (Analysis.rationalLogIntervalCheck_sound (N := 672) (j := 9) (n := 27) (lo := 5) (hi := 6.511)
        (by decide +kernel)).2
  norm_num only [Rat.cast_ofScientific] at hhi
  have hrU : r ≤ (672 : ℝ) := by linarith only [hr.2]
  have hl := (Real.log_le_log ((by norm_num only : (0 : ℝ) < 332.15).trans_le hr.1) hrU).trans hhi
  have h :=
    joint_lower_box hRH (u := 14.544) (L := 13.022) (E := 0.000491)
      ⟨hr.1, hr.2.trans (by norm_num only)⟩
      (by
        norm_num only [Rat.cast_ofScientific]; linarith only [hl])
      (by norm_num only [Rat.cast_ofScientific]) (by decide +kernel) α hα hprefix
  norm_num only [Rat.cast_ofScientific] at h ⊢
  exact h

/-- The main reflected kernel costs at most 0.0008 on radii 328 through 672. -/
theorem k197_main_reflect_to672 {r : ℝ} (hr : r ∈ Set.Icc 328 672) :
    quarterAuxReflectCap656 r (-(21 / 8)) 103684 ≤ 0.0008 := by
  have hr₁ : (1 : ℝ) ≤ r := (by norm_num only : (1 : ℝ) ≤ 328).trans hr.1
  have hh : -(21 / 8 : ℝ) ≤ 2 * Real.log r := by linarith only [Real.log_nonneg hr₁]
  have he := shift_exp_upper (-(21 / 8)) 0.0558 (by decide +kernel) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat, Rat.cast_ofScientific] at he
  have he' : Real.exp ((11 / 10 : ℝ) * -(21 / 8)) ≤ 0.0558 := by
    norm_num only
    exact he
  have hr₀ := zero_lt_one.trans_le hr₁
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound (N := 672) (j := 9) (n := 27) (lo := 5) (hi := 6.511)
        (by decide +kernel)).2
  simp only [Rat.cast_ofScientific] at hlog
  have hcap : 2 * Real.log r ≤ 13.022 := cap_log_bound hr₀ hr.2 (by linarith only [hlog])
  refine (cap_rectangle_354 hr₀ hh he' hcap (cap_decay_328 hr.1)).trans ?_
  norm_num only [momentBox, Analysis.logPowerTailPoly, Finset.sum_range_succ, Finset.sum_range_zero,
    Nat.choose, Nat.reduceAdd, Nat.reduceSub, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]

private theorem k197_reflect_to672 {r : ℝ} (hr : r ∈ Set.Icc 328 672) :
    14.21 ≤ 21 / 8 + Real.log (r ^ 2) ∧
      0.000000033 ≤ Real.exp (-(11 / 10) * (21 / 8 + Real.log (r ^ 2))) := by
  have h₀ := (by norm_num only : (0 : ℝ) < 328).trans_le hr.1
  have hl :=
    (Analysis.rationalLogIntervalCheck_sound (N := 328) (j := 9) (n := 27) (lo := 5.793) (hi := 6)
        (by decide +kernel)).1
  have hu :=
    (Analysis.rationalLogIntervalCheck_sound (N := 672) (j := 9) (n := 27) (lo := 5) (hi := 6.511)
        (by decide +kernel)).2
  have he :=
    (Analysis.rationalLogIntervalCheck_sound (N := 1000000000 / 33) (j := 25) (n := 32) (lo :=
        17.2267) (hi := 18) (by decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div, Rat.cast_ofScientific] at hl hu he
  have hz : 14.21 ≤ 21 / 8 + Real.log (r ^ 2) := by
    rw [Real.log_pow]
    linarith only [hl, Real.log_le_log (by norm_num only : (0 : ℝ) < 328) hr.1]
  have hru : r ≤ (672 : ℝ) := by linarith only [hr.2]
  have hd : 0.000000033 ≤ Real.exp (-(11 / 10) * (21 / 8 + Real.log (r ^ 2))) := by
    apply (Real.log_le_iff_le_exp (by norm_num only)).mp
    have hi : Real.log (0.000000033 : ℝ)⁻¹ ≥ 17.2267 := by
      norm_num only at he ⊢; exact he
    rw [Real.log_inv] at hi
    rw [Real.log_pow]
    linarith only [hi, hu, Real.log_le_log h₀ hru]
  exact ⟨hz, hd⟩

/-- The prefix through 2701 gives a uniform lower bound for three copies
of the principal reflected Euler series through radius 672. -/
theorem gaussian_k197_reflect_credit_to672 {r : ℝ} (hr : r ∈ Set.Icc 328 672) :
    0.00197 ≤ 3 * quarterMainEuler656 (1 : DirichletCharacter ℂ 1) (r ^ 2) := by
  obtain ⟨hz, hd⟩ := k197_reflect_to672 hr
  exact reflect_credit_of_exp hr.1 hz hd (by norm_num only)

private theorem first_rectangle_to672 {z : ℝ} (hl : 14.232 ≤ z) (hu : z ≤ 15.647) :
    0.0113 ≤ quarterGammaFirst656 z := by
  have ht :=
    (Analysis.rationalLogIntervalCheck_sound (N := 1000000 / 196) (j := 13) (n := 48) (lo := 8)
        (hi := 8.538) (by decide +kernel)).2
  have hf :=
    (Analysis.rationalLogIntervalCheck_sound (N := 1000000 / 399) (j := 11) (n := 48) (lo := 7.8265)
        (hi := 8) (by decide +kernel)).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at ht hf
  have htail : Real.exp (-(3 / 5 : ℝ) * 14.232) ≤ 0.000196 := by
    rw [neg_mul]
    apply exp_neg_le_of_log_inv (by norm_num only)
    norm_num only at ht ⊢
    linarith only [ht]
  have hfront : 0.000399 ≤ Real.exp (-(1 / 2 : ℝ) * 15.647) := by
    rw [neg_mul]
    apply le_exp_neg_of_log_inv (by norm_num only)
    norm_num only at hf ⊢
    linarith only [hf]
  have hm :=
    first_moment_lower_of_exp htail (m := 2194)
      (by norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat, Nat.cast_one])
      (by norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat, Nat.cast_one])
  exact
    first_rectangle_lower (c := 0.0113) (by norm_num only) hl hu hfront hm (by norm_num only)
      (by norm_num only)

/-- The first Gamma pole gives a uniform credit for radii between 663/2
and 672, covering the middle K197 radii. -/
theorem quarter_gamma_k197_to672 {r : ℝ} (hr : r ∈ Set.Icc (663 / 2) 672) :
    (centralGammaPair656 (1 : DirichletCharacter ℂ 1) (r ^ 2)).re ≤
      -2.16 * quarterWeight656 (r ^ 2) 1 - 0.0113 := by
  have hl :=
    (Analysis.rationalLogIntervalCheck_sound (N := 663 / 2) (j := 9) (n := 32) (lo := 5.8035) (hi :=
        6) (by decide +kernel)).1
  have hu :=
    (Analysis.rationalLogIntervalCheck_sound (N := 672) (j := 9) (n := 32) (lo := 5) (hi := 6.511)
        (by decide +kernel)).2
  simp only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hl hu
  have hr₀ : 0 < r := (by norm_num only : (0 : ℝ) < 663 / 2).trans_le hr.1
  have hlo := Real.log_le_log (by norm_num only : (0 : ℝ) < 663 / 2) hr.1
  have hup := Real.log_le_log hr₀ hr.2
  have hfirst : 0.0113 ≤ quarterGammaFirst656 (Real.log (r ^ 2) + 21 / 8) := by
    rw [Real.log_pow]
    exact first_rectangle_to672 (by linarith only [hl, hlo]) (by linarith only [hu, hup])
  exact
    (quarter_principal_gamma_upper_656 ((by norm_num only : (322 : ℝ) ≤ 663 / 2).trans hr.1)).trans
      (sub_le_sub_left hfirst _)

private theorem k197_log_credit_to672 {r : ℝ} (hr : r ∈ Set.Icc (663 / 2) 672) :
    0.00101 ≤ 4 * quarterWeight656 (r ^ 2) (r ^ 2) * Real.log (2 * Real.pi) := by
  have hp := (by norm_num only : (0 : ℝ) < 663 / 2).trans_le hr.1
  rw [quarter_cutoff_weight_656 (sq_pos_of_pos hp), Real.sqrt_sq hp.le]
  have hlog : (1.837 : ℝ) ≤ Real.log (2 * Real.pi) := by linarith only [Analysis.log_two_mul_pi_gt]
  have hW : (0.09319731 : ℝ) ≤ (quarterKernel656.transform 1).re := by
    linarith only [quarter_unit_weight_656.1]
  have hw :=
    (div_le_div_of_nonneg_left (by norm_num only : (0 : ℝ) ≤ 0.09319731) hp hr.2).trans
      (div_le_div_of_nonneg_right hW hp.le)
  have h :=
    mul_le_mul hw hlog (by norm_num only : (0 : ℝ) ≤ 1.837)
      ((by norm_num only : (0 : ℝ) ≤ 0.09319731 / 672).trans hw)
  linarith only [h]

/-- On the middle K197 radii through 672, any certified signed boundary
cost gives a principal-sum lower bound including the Gamma term. -/
theorem gaussian_k197_principal_to672 (hRH : RiemannHypothesis) {r B : ℝ}
    (hr : r ∈ Set.Icc (663 / 2) 672)
    (hb : -4 * (Chebyshev.psi (r ^ 2) - r ^ 2) * quarterWeight656 (r ^ 2) (r ^ 2) ≤ B) :
    let x := r ^ 2
    let W := fun n ↦ (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) x n).re
    (0.71780481 : ℝ) * r + 0.007898 - B <
      4 * (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, W n) - (∑' n, W n) -
        3 * (centralGammaPair656 (1 : DirichletCharacter ℂ 1) x).re := by
  intro x W
  have h :=
    gaussian_principal_gamma_lower hRH ((by norm_num only : (331 : ℝ) ≤ 663 / 2).trans hr.1)
      (quarter_gamma_k197_to672 hr) hb (k197_log_credit_to672 hr)
  dsimp only [x, W] at h ⊢
  linarith only [h]

private theorem radius_log_571 : Real.log (571 : ℝ) ∈ Set.Icc 6.34738 6.34739 := by
  have h :=
    Analysis.rationalLogIntervalCheck_sound (N := 571) (j := 9) (n := 27) (lo := 6.34738) (hi :=
      6.34739) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at h ⊢
  exact h

private theorem radius_power_571 : (571 : ℝ) ^ (-(6 / 5) : ℝ) ≤ 0.000492083 := by
  have h :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 571) (p := 6) (d := 5)
        (lo := 0) (hi := 0.000492083) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat,
    neg_div] at h ⊢
  exact h

/-- The shifted conductor term is at least -2.12102 at radii from 571. -/
theorem theta_from571 {r : ℝ} (hr : (571 : ℝ) ≤ r) : (-2.12102 : ℝ) ≤ gaussianTheta197 r := by
  have hlog : (23 / 2 : ℝ) ≤ 2 * Real.log (571) := by linarith only [radius_log_571.1]
  have hP :=
    conductor_poly_mono (sub_nonneg.mpr hlog) (by norm_num only : (0 : ℝ) ≤ 1.19478)
      (show 2 * Real.log (571) - 23 / 2 ≤ 1.19478 by linarith only [radius_log_571.2])
  have hprod :=
    (mul_le_mul_of_nonneg_left hP (Real.rpow_nonneg (by norm_num only) _)).trans
      (mul_le_mul_of_nonneg_right radius_power_571 (by norm_num only [gaussianConductorPoly197]))
  apply gaussian_theta_endpoint_197 (by norm_num only) hr hlog
  rw [mul_assoc]
  exact
    (mul_le_mul_of_nonneg_left hprod (by norm_num only : (0 : ℝ) ≤ (11 / 10) ^ 5 / 30)).trans
      (by norm_num only [gaussianConductorPoly197])

/-- The principal inverse-scale conductor is bounded by its certified
value at radius 571 for all larger radii. -/
theorem quarter_main_conductor_from571 {r : ℝ} (hr : (571 : ℝ) ≤ r) :
    4 * r * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 1.24201 := by
  have hb :=
    conductor_endpoint_box (r := 571) (z := 12.69478) (C := 1.24201) (by norm_num only)
      (by linarith only [radius_log_571.2]) radius_power_571 (by norm_num only)
  have hl : (571 : ℝ) ∈ Set.Ici 328 := by norm_num only [Set.mem_Ici]
  have he := main_conductor_antitone hl (hl.trans hr) hr
  exact he.trans hb

/-- The inverse-scale principal conductor is at most 1.22174 after
division by a Gaussian scale of at least 1.0166. -/
theorem gaussian_main_conductor_from571 {r s : ℝ} (hr : (571 : ℝ) ≤ r) (hs : 1.0166 ≤ s) :
    4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 1.22174 := by
  have hs₀ : 0 < s := (by norm_num only : (0 : ℝ) < 1.0166).trans_le hs
  rw [show
      4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re =
        (4 * r * (quarterKernel656.transform (r ^ 2)⁻¹).re) / s
      by ring]
  apply (div_le_iff₀ hs₀).mpr
  linarith only [quarter_main_conductor_from571 hr, hs]

private theorem radius_log_604 : Real.log (604 : ℝ) ∈ Set.Icc 6.40357 6.40358 := by
  have h :=
    Analysis.rationalLogIntervalCheck_sound (N := 604) (j := 9) (n := 27) (lo := 6.40357) (hi :=
      6.40358) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at h ⊢
  exact h

private theorem radius_power_604 : (604 : ℝ) ^ (-(6 / 5) : ℝ) ≤ 0.000460000 := by
  have h :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 604) (p := 6) (d := 5)
        (lo := 0) (hi := 0.000460000) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat,
    neg_div] at h ⊢
  exact h

/-- The shifted conductor term is at least -2.04170 at radii from 604. -/
theorem theta_from604 {r : ℝ} (hr : (604 : ℝ) ≤ r) : (-2.04170 : ℝ) ≤ gaussianTheta197 r := by
  have hlog : (23 / 2 : ℝ) ≤ 2 * Real.log (604) := by linarith only [radius_log_604.1]
  have hP :=
    conductor_poly_mono (sub_nonneg.mpr hlog) (by norm_num only : (0 : ℝ) ≤ 1.30716)
      (show 2 * Real.log (604) - 23 / 2 ≤ 1.30716 by linarith only [radius_log_604.2])
  have hprod :=
    (mul_le_mul_of_nonneg_left hP (Real.rpow_nonneg (by norm_num only) _)).trans
      (mul_le_mul_of_nonneg_right radius_power_604 (by norm_num only [gaussianConductorPoly197]))
  apply gaussian_theta_endpoint_197 (by norm_num only) hr hlog
  rw [mul_assoc]
  exact
    (mul_le_mul_of_nonneg_left hprod (by norm_num only : (0 : ℝ) ≤ (11 / 10) ^ 5 / 30)).trans
      (by norm_num only [gaussianConductorPoly197])

/-- The principal inverse-scale conductor is bounded by its certified
value at radius 604 for all larger radii. -/
theorem quarter_main_conductor_from604 {r : ℝ} (hr : (604 : ℝ) ≤ r) :
    4 * r * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 1.20424 := by
  have hb :=
    conductor_endpoint_box (r := 604) (z := 12.80716) (C := 1.20424) (by norm_num only)
      (by linarith only [radius_log_604.2]) radius_power_604 (by norm_num only)
  have hl : (604 : ℝ) ∈ Set.Ici 328 := by norm_num only [Set.mem_Ici]
  have he := main_conductor_antitone hl (hl.trans hr) hr
  exact he.trans hb

/-- The inverse-scale principal conductor is at most 1.18459 after
division by a Gaussian scale of at least 1.0166. -/
theorem gaussian_main_conductor_from604 {r s : ℝ} (hr : (604 : ℝ) ≤ r) (hs : 1.0166 ≤ s) :
    4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 1.18459 := by
  have hs₀ : 0 < s := (by norm_num only : (0 : ℝ) < 1.0166).trans_le hs
  rw [show
      4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re =
        (4 * r * (quarterKernel656.transform (r ^ 2)⁻¹).re) / s
      by ring]
  apply (div_le_iff₀ hs₀).mpr
  linarith only [quarter_main_conductor_from604 hr, hs]

private theorem radius_log_636 : Real.log (636 : ℝ) ∈ Set.Icc 6.45519 6.45520 := by
  have h :=
    Analysis.rationalLogIntervalCheck_sound (N := 636) (j := 9) (n := 27) (lo := 6.45519) (hi :=
      6.45520) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at h ⊢
  exact h

private theorem radius_power_636 : (636 : ℝ) ^ (-(6 / 5) : ℝ) ≤ 0.000432368 := by
  have h :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 636) (p := 6) (d := 5)
        (lo := 0) (hi := 0.000432368) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat,
    neg_div] at h ⊢
  exact h

/-- The shifted conductor term is at least -1.97044 at radii from 636. -/
theorem theta_from636 {r : ℝ} (hr : (636 : ℝ) ≤ r) : (-1.97044 : ℝ) ≤ gaussianTheta197 r := by
  have hlog : (23 / 2 : ℝ) ≤ 2 * Real.log (636) := by linarith only [radius_log_636.1]
  have hP :=
    conductor_poly_mono (sub_nonneg.mpr hlog) (by norm_num only : (0 : ℝ) ≤ 1.41040)
      (show 2 * Real.log (636) - 23 / 2 ≤ 1.41040 by linarith only [radius_log_636.2])
  have hprod :=
    (mul_le_mul_of_nonneg_left hP (Real.rpow_nonneg (by norm_num only) _)).trans
      (mul_le_mul_of_nonneg_right radius_power_636 (by norm_num only [gaussianConductorPoly197]))
  apply gaussian_theta_endpoint_197 (by norm_num only) hr hlog
  rw [mul_assoc]
  exact
    (mul_le_mul_of_nonneg_left hprod (by norm_num only : (0 : ℝ) ≤ (11 / 10) ^ 5 / 30)).trans
      (by norm_num only [gaussianConductorPoly197])

/-- The principal inverse-scale conductor is bounded by its certified
value at radius 636 for all larger radii. -/
theorem quarter_main_conductor_from636 {r : ℝ} (hr : (636 : ℝ) ≤ r) :
    4 * r * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 1.17028 := by
  have hb :=
    conductor_endpoint_box (r := 636) (z := 12.91040) (C := 1.17028) (by norm_num only)
      (by linarith only [radius_log_636.2]) radius_power_636 (by norm_num only)
  have hl : (636 : ℝ) ∈ Set.Ici 328 := by norm_num only [Set.mem_Ici]
  have he := main_conductor_antitone hl (hl.trans hr) hr
  exact he.trans hb

/-- The inverse-scale principal conductor is at most 1.15118 after
division by a Gaussian scale of at least 1.0166. -/
theorem gaussian_main_conductor_from636 {r s : ℝ} (hr : (636 : ℝ) ≤ r) (hs : 1.0166 ≤ s) :
    4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 1.15118 := by
  have hs₀ : 0 < s := (by norm_num only : (0 : ℝ) < 1.0166).trans_le hs
  rw [show
      4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re =
        (4 * r * (quarterKernel656.transform (r ^ 2)⁻¹).re) / s
      by ring]
  apply (div_le_iff₀ hs₀).mpr
  linarith only [quarter_main_conductor_from636 hr, hs]

end PseudoPrime.PrimeTestBounds.MillerRabin
