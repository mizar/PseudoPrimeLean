/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK137Later
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

/-! # Principal and reflected bounds for K197 through radius 354 -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For radii from 332.15 to 354, the combined K197 reflection
is at least -0.000075 by the common endpoint moment estimate. -/
theorem gaussian_joint_to354 (hRH : RiemannHypothesis) {r : ℝ} (hr : r ∈ Set.Icc 332.15 354)
    (α : ℕ → ℝ) (hα : ∀ n, 0 ≤ α n ∧ α n ≤ 4)
    (hprefix : ∀ n : ℕ, (n : ℝ) ≤ r ^ 2 → ArithmeticFunction.vonMangoldt n ≠ 0 → α n = 0) :
    (-0.000075 : ℝ) ≤
      ∑ i, (gaussianCoeff197 i : ℝ) * quarterAuxReflection656 α r (quarterShift663 i : ℝ) := by
  have hhi :=
    (Analysis.rationalLogIntervalCheck_sound (N := 354) (j := 9) (n := 27) (lo := 5) (hi := 5.87)
        (by decide +kernel)).2
  norm_num only [Rat.cast_ofScientific] at hhi
  have hrU : r ≤ (354 : ℝ) := by linarith only [hr.2]
  have hl := (Real.log_le_log ((by norm_num only : (0 : ℝ) < 332.15).trans_le hr.1) hrU).trans hhi
  have h :=
    joint_lower_box hRH (u := 11.98) (L := 11.74) (E := 0.000075)
      ⟨hr.1, hr.2.trans (by norm_num only)⟩
      (by
        norm_num only [Rat.cast_ofScientific]; linarith only [hl])
      (by norm_num only [Rat.cast_ofScientific]) (by decide +kernel) α hα hprefix
  norm_num only [Rat.cast_ofScientific] at h ⊢
  exact h

private theorem cap_rectangle_354 {r h e v D : ℝ} (hr : 0 < r) (hh : h ≤ 2 * Real.log r)
    (he : Real.exp ((11 / 10) * h) ≤ e) (hv : 2 * Real.log r ≤ v) (hD : r ^ (-(11 / 5) : ℝ) ≤ D) :
    quarterAuxReflectCap656 r h 103684 ≤
      ((11 / 10 : ℝ) ^ 5 / 30 * D * e) *
        ∑ j ∈ Finset.range 6, (Nat.choose 5 j : ℝ) * (v - h) ^ (5 - j) * momentBox j := by
  have hz := sub_le_sub_right hv h
  have hv := sub_nonneg.mpr hh
  have he₀ := (Real.exp_pos _).le.trans he
  unfold quarterAuxReflectCap656
  rw [show
      ∀ S : ℝ,
        ((11 / 10 : ℝ) ^ 5 / 120 * r ^ (-(11 / 5) : ℝ) * Real.exp ((11 / 10) * h)) * (4 * S) =
          ((11 / 10 : ℝ) ^ 5 / 30 * r ^ (-(11 / 5) : ℝ) * Real.exp ((11 / 10) * h)) * S
      from fun S ↦ by ring]
  have hD₀ := (Real.rpow_nonneg hr.le (-(11 / 5) : ℝ)).trans hD
  gcongr
  all_goals
    first
    | exact cap_numeric _
    | exact cap_nonneg _
    | exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (hv.trans hz) _)
    |
      exact
        Finset.sum_nonneg
          (fun j _ ↦ mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hv _)) (cap_nonneg j))

/-- The main reflected kernel costs at most 0.0003 on radii 328 through 354. -/
theorem k197_main_reflect_to354 {r : ℝ} (hr : r ∈ Set.Icc 328 354) :
    quarterAuxReflectCap656 r (-(21 / 8)) 103684 ≤ 0.0003 := by
  have hr₁ : (1 : ℝ) ≤ r := (by norm_num only : (1 : ℝ) ≤ 328).trans hr.1
  have hh : -(21 / 8 : ℝ) ≤ 2 * Real.log r := by linarith only [Real.log_nonneg hr₁]
  have he := shift_exp_upper (-(21 / 8)) 0.0558 (by decide +kernel) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat, Rat.cast_ofScientific] at he
  have he' : Real.exp ((11 / 10 : ℝ) * -(21 / 8)) ≤ 0.0558 := by
    norm_num only
    exact he
  have hr₀ := zero_lt_one.trans_le hr₁
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound (N := 354) (j := 9) (n := 27) (lo := 5) (hi := 5.87)
        (by decide +kernel)).2
  simp only [Rat.cast_ofScientific] at hlog
  have hcap : 2 * Real.log r ≤ 11.74 := cap_log_bound hr₀ hr.2 (by linarith only [hlog])
  refine (cap_rectangle_354 hr₀ hh he' hcap (cap_decay_328 hr.1)).trans ?_
  norm_num only [momentBox, Analysis.logPowerTailPoly, Finset.sum_range_succ, Finset.sum_range_zero,
    Nat.choose, Nat.reduceAdd, Nat.reduceSub, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]

private theorem k197_reflect_to354 {r : ℝ} (hr : r ∈ Set.Icc 328 354) :
    14.21 ≤ 21 / 8 + Real.log (r ^ 2) ∧
      0.000000137 ≤ Real.exp (-(11 / 10) * (21 / 8 + Real.log (r ^ 2))) := by
  have h₀ := (by norm_num only : (0 : ℝ) < 328).trans_le hr.1
  have hl :=
    (Analysis.rationalLogIntervalCheck_sound (N := 328) (j := 9) (n := 27) (lo := 5.793) (hi := 6)
        (by decide +kernel)).1
  have hu :=
    (Analysis.rationalLogIntervalCheck_sound (N := 354) (j := 9) (n := 27) (lo := 5) (hi := 5.87)
        (by decide +kernel)).2
  have he :=
    (Analysis.rationalLogIntervalCheck_sound (N := 1000000000 / 137) (j := 23) (n := 32) (lo :=
        15.8032) (hi := 16) (by decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div, Rat.cast_ofScientific] at hl hu he
  have hz : 14.21 ≤ 21 / 8 + Real.log (r ^ 2) := by
    rw [Real.log_pow]
    linarith only [hl, Real.log_le_log (by norm_num only : (0 : ℝ) < 328) hr.1]
  have hru : r ≤ (354 : ℝ) := by linarith only [hr.2]
  have hd : 0.000000137 ≤ Real.exp (-(11 / 10) * (21 / 8 + Real.log (r ^ 2))) := by
    apply (Real.log_le_iff_le_exp (by norm_num only)).mp
    have hi : Real.log (0.000000137 : ℝ)⁻¹ ≥ 15.8032 := by
      norm_num only at he ⊢; exact he
    rw [Real.log_inv] at hi
    rw [Real.log_pow]
    linarith only [hi, hu, Real.log_le_log h₀ hru]
  exact ⟨hz, hd⟩

/-- The prefix through 2701 gives a uniform lower bound for three copies
of the principal reflected Euler series through radius 354. -/
theorem gaussian_k197_reflect_credit_to354 {r : ℝ} (hr : r ∈ Set.Icc 328 354) :
    0.00818 ≤ 3 * quarterMainEuler656 (1 : DirichletCharacter ℂ 1) (r ^ 2) := by
  obtain ⟨hz, hd⟩ := k197_reflect_to354 hr
  exact reflect_credit_of_exp hr.1 hz hd (by norm_num only)

private theorem first_rectangle_to354 {z : ℝ} (hl : 14.232 ≤ z) (hu : z ≤ 14.365) :
    0.0222 ≤ quarterGammaFirst656 z := by
  have ht :=
    (Analysis.rationalLogIntervalCheck_sound (N := 1000000 / 196) (j := 13) (n := 48) (lo := 8)
        (hi := 8.538) (by decide +kernel)).2
  have hf :=
    (Analysis.rationalLogIntervalCheck_sound (N := 1000000 / 759) (j := 11) (n := 48) (lo := 7.1834)
        (hi := 8) (by decide +kernel)).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at ht hf
  have htail : Real.exp (-(3 / 5 : ℝ) * 14.232) ≤ 0.000196 := by
    rw [neg_mul]
    apply exp_neg_le_of_log_inv (by norm_num only)
    norm_num only at ht ⊢
    linarith only [ht]
  have hfront : 0.000759 ≤ Real.exp (-(1 / 2 : ℝ) * 14.365) := by
    rw [neg_mul]
    apply le_exp_neg_of_log_inv (by norm_num only)
    norm_num only at hf ⊢
    linarith only [hf]
  have hm :=
    first_moment_lower_of_exp htail (m := 2194)
      (by norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat, Nat.cast_one])
      (by norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat, Nat.cast_one])
  exact
    first_rectangle_lower (c := 0.0222) (by norm_num only) hl hu hfront hm (by norm_num only)
      (by norm_num only)

/-- The first Gamma pole gives a uniform credit for radii between 663/2
and 354, covering the middle K197 radii. -/
theorem quarter_gamma_k197_to354 {r : ℝ} (hr : r ∈ Set.Icc (663 / 2) 354) :
    (centralGammaPair656 (1 : DirichletCharacter ℂ 1) (r ^ 2)).re ≤
      -2.16 * quarterWeight656 (r ^ 2) 1 - 0.0222 := by
  have hl :=
    (Analysis.rationalLogIntervalCheck_sound (N := 663 / 2) (j := 9) (n := 32) (lo := 5.8035) (hi :=
        6) (by decide +kernel)).1
  have hu :=
    (Analysis.rationalLogIntervalCheck_sound (N := 354) (j := 9) (n := 32) (lo := 5) (hi := 5.87)
        (by decide +kernel)).2
  simp only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hl hu
  have hr₀ : 0 < r := (by norm_num only : (0 : ℝ) < 663 / 2).trans_le hr.1
  have hlo := Real.log_le_log (by norm_num only : (0 : ℝ) < 663 / 2) hr.1
  have hup := Real.log_le_log hr₀ hr.2
  have hfirst : 0.0222 ≤ quarterGammaFirst656 (Real.log (r ^ 2) + 21 / 8) := by
    rw [Real.log_pow]
    exact first_rectangle_to354 (by linarith only [hl, hlo]) (by linarith only [hu, hup])
  exact
    (quarter_principal_gamma_upper_656 ((by norm_num only : (322 : ℝ) ≤ 663 / 2).trans hr.1)).trans
      (sub_le_sub_left hfirst _)

private theorem k197_log_credit_to354 {r : ℝ} (hr : r ∈ Set.Icc (663 / 2) 354) :
    0.00193 ≤ 4 * quarterWeight656 (r ^ 2) (r ^ 2) * Real.log (2 * Real.pi) := by
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
      ((by norm_num only : (0 : ℝ) ≤ 0.09319731 / 354).trans hw)
  linarith only [h]

/-- On the middle K197 radii through 354, any certified signed boundary
cost gives a principal-sum lower bound including the Gamma term. -/
theorem gaussian_k197_principal_to354 (hRH : RiemannHypothesis) {r B : ℝ}
    (hr : r ∈ Set.Icc (663 / 2) 354)
    (hb : -4 * (Chebyshev.psi (r ^ 2) - r ^ 2) * quarterWeight656 (r ^ 2) (r ^ 2) ≤ B) :
    let x := r ^ 2
    let W := fun n ↦ (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) x n).re
    (0.71780481 : ℝ) * r + 0.041518 - B <
      4 * (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, W n) - (∑' n, W n) -
        3 * (centralGammaPair656 (1 : DirichletCharacter ℂ 1) x).re := by
  intro x W
  have h :=
    gaussian_principal_gamma_lower hRH ((by norm_num only : (331 : ℝ) ≤ 663 / 2).trans hr.1)
      (quarter_gamma_k197_to354 hr) hb (k197_log_credit_to354 hr)
  dsimp only [x, W] at h ⊢
  linarith only [h]

private theorem radius_log_346 : Real.log (346 : ℝ) ∈ Set.Icc 5.84643 5.84644 := by
  have h :=
    Analysis.rationalLogIntervalCheck_sound (N := 346) (j := 9) (n := 27) (lo := 5.84643) (hi :=
      5.84644) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at h ⊢
  exact h

private theorem radius_power_346 : (346 : ℝ) ^ (-(6 / 5) : ℝ) ≤ 0.000897655 := by
  have h :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 346) (p := 6) (d := 5)
        (lo := 0) (hi := 0.000897655) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat,
    neg_div] at h ⊢
  exact h

/-- The shifted conductor term is at least -2.89073 at radii from 346. -/
theorem theta_from346 {r : ℝ} (hr : (346 : ℝ) ≤ r) : (-2.89073 : ℝ) ≤ gaussianTheta197 r := by
  have hlog : (23 / 2 : ℝ) ≤ 2 * Real.log (346) := by linarith only [radius_log_346.1]
  have hP :=
    conductor_poly_mono (sub_nonneg.mpr hlog) (by norm_num only : (0 : ℝ) ≤ 0.19288)
      (show 2 * Real.log (346) - 23 / 2 ≤ 0.19288 by linarith only [radius_log_346.2])
  have hprod :=
    (mul_le_mul_of_nonneg_left hP (Real.rpow_nonneg (by norm_num only) _)).trans
      (mul_le_mul_of_nonneg_right radius_power_346 (by norm_num only [gaussianConductorPoly197]))
  apply gaussian_theta_endpoint_197 (by norm_num only) hr hlog
  rw [mul_assoc]
  exact
    (mul_le_mul_of_nonneg_left hprod (by norm_num only : (0 : ℝ) ≤ (11 / 10) ^ 5 / 30)).trans
      (by norm_num only [gaussianConductorPoly197])

/-- The principal inverse-scale conductor is bounded by its certified
value at radius 346 for all larger radii. -/
theorem quarter_main_conductor_from346 {r : ℝ} (hr : (346 : ℝ) ≤ r) :
    4 * r * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 1.61556 := by
  have hb :=
    main_conductor_box (r := 346) (u := 346) (z := 11.69288) (C := 1.61556) (by norm_num only)
      le_rfl (by linarith only [radius_log_346.2]) radius_power_346 (by norm_num only)
      (by norm_num only)
  have hl : (346 : ℝ) ∈ Set.Ici 328 := by norm_num only [Set.mem_Ici]
  have he := main_conductor_antitone hl (hl.trans hr) hr
  exact he.trans (by simpa only [sub_self, mul_zero, add_zero] using hb)

/-- The inverse-scale principal conductor is at most 1.61250 after
division by a Gaussian scale of at least 1.0019. -/
theorem gaussian_main_conductor_from346 {r s : ℝ} (hr : (346 : ℝ) ≤ r) (hs : 1.0019 ≤ s) :
    4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 1.61250 := by
  have hs₀ : 0 < s := (by norm_num only : (0 : ℝ) < 1.0019).trans_le hs
  rw [show
      4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re =
        (4 * r * (quarterKernel656.transform (r ^ 2)⁻¹).re) / s
      by ring]
  apply (div_le_iff₀ hs₀).mpr
  linarith only [quarter_main_conductor_from346 hr, hs]

private theorem radius_log_34707 : Real.log (34707 / 100 : ℝ) ∈ Set.Icc 5.84952 5.84953 := by
  have h :=
    Analysis.rationalLogIntervalCheck_sound (N := 34707 / 100) (j := 9) (n := 27) (lo := 5.84952)
      (hi := 5.84953) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at h ⊢
  exact h

private theorem radius_power_34707 : (34707 / 100 : ℝ) ^ (-(6 / 5) : ℝ) ≤ 0.000894335 := by
  have h :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 34707 / 100) (p := 6)
        (d := 5) (lo := 0) (hi := 0.000894335) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat,
    neg_div] at h ⊢
  exact h

/-- The shifted conductor term is at least -2.88579 at radii from 347.07. -/
theorem theta_from34707 {r : ℝ} (hr : (34707 / 100 : ℝ) ≤ r) :
    (-2.88579 : ℝ) ≤ gaussianTheta197 r := by
  have hlog : (23 / 2 : ℝ) ≤ 2 * Real.log (34707 / 100) := by linarith only [radius_log_34707.1]
  have hP :=
    conductor_poly_mono (sub_nonneg.mpr hlog) (by norm_num only : (0 : ℝ) ≤ 0.19906)
      (show 2 * Real.log (34707 / 100) - 23 / 2 ≤ 0.19906 by linarith only [radius_log_34707.2])
  have hprod :=
    (mul_le_mul_of_nonneg_left hP (Real.rpow_nonneg (by norm_num only) _)).trans
      (mul_le_mul_of_nonneg_right radius_power_34707 (by norm_num only [gaussianConductorPoly197]))
  apply gaussian_theta_endpoint_197 (by norm_num only) hr hlog
  rw [mul_assoc]
  exact
    (mul_le_mul_of_nonneg_left hprod (by norm_num only : (0 : ℝ) ≤ (11 / 10) ^ 5 / 30)).trans
      (by norm_num only [gaussianConductorPoly197])

/-- The principal inverse-scale conductor is bounded by its certified
value at radius 347.07 for all larger radii. -/
theorem quarter_main_conductor_from34707 {r : ℝ} (hr : (34707 / 100 : ℝ) ≤ r) :
    4 * r * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 1.61306 := by
  have hb :=
    main_conductor_box (r := 34707 / 100) (u := 34707 / 100) (z := 11.69906) (C := 1.61306)
      (by norm_num only) le_rfl (by linarith only [radius_log_34707.2]) radius_power_34707
      (by norm_num only) (by norm_num only)
  have hl : (34707 / 100 : ℝ) ∈ Set.Ici 328 := by norm_num only [Set.mem_Ici]
  have he := main_conductor_antitone hl (hl.trans hr) hr
  exact he.trans (by simpa only [sub_self, mul_zero, add_zero] using hb)

/-- The inverse-scale principal conductor is at most 1.61001 after
division by a Gaussian scale of at least 1.0019. -/
theorem gaussian_main_conductor_from34707 {r s : ℝ} (hr : (34707 / 100 : ℝ) ≤ r) (hs : 1.0019 ≤ s) :
    4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 1.61001 := by
  have hs₀ : 0 < s := (by norm_num only : (0 : ℝ) < 1.0019).trans_le hs
  rw [show
      4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re =
        (4 * r * (quarterKernel656.transform (r ^ 2)⁻¹).re) / s
      by ring]
  apply (div_le_iff₀ hs₀).mpr
  linarith only [quarter_main_conductor_from34707 hr, hs]

end PseudoPrime.PrimeTestBounds.MillerRabin
