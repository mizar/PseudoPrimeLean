/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Main354
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

/-! # Principal and reflected bounds for K197 through radius 426 -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For radii from 332.15 to 426, the combined K197 reflection
is at least -0.000141 by the common endpoint moment estimate. -/
theorem gaussian_joint_to426 (hRH : RiemannHypothesis) {r : ℝ} (hr : r ∈ Set.Icc 332.15 426)
    (α : ℕ → ℝ) (hα : ∀ n, 0 ≤ α n ∧ α n ≤ 4)
    (hprefix : ∀ n : ℕ, (n : ℝ) ≤ r ^ 2 → ArithmeticFunction.vonMangoldt n ≠ 0 → α n = 0) :
    (-0.000141 : ℝ) ≤
      ∑ i, (gaussianCoeff197 i : ℝ) * quarterAuxReflection656 α r (quarterShift663 i : ℝ) := by
  have hhi :=
    (Analysis.rationalLogIntervalCheck_sound (N := 426) (j := 9) (n := 27) (lo := 5) (hi := 6.055)
        (by decide +kernel)).2
  norm_num only [Rat.cast_ofScientific] at hhi
  have hrU : r ≤ (426 : ℝ) := by linarith only [hr.2]
  have hl := (Real.log_le_log ((by norm_num only : (0 : ℝ) < 332.15).trans_le hr.1) hrU).trans hhi
  have h :=
    joint_lower_box hRH (u := 12.72) (L := 12.11) (E := 0.000141)
      ⟨hr.1, hr.2.trans (by norm_num only)⟩
      (by
        norm_num only [Rat.cast_ofScientific]; linarith only [hl])
      (by norm_num only [Rat.cast_ofScientific]) (by decide +kernel) α hα hprefix
  norm_num only [Rat.cast_ofScientific] at h ⊢
  exact h

/-- The main reflected kernel costs at most 0.00044 on radii 328 through 426. -/
theorem k197_main_reflect_to426 {r : ℝ} (hr : r ∈ Set.Icc 328 426) :
    quarterAuxReflectCap656 r (-(21 / 8)) 103684 ≤ 0.00044 := by
  have hr₁ : (1 : ℝ) ≤ r := (by norm_num only : (1 : ℝ) ≤ 328).trans hr.1
  have hh : -(21 / 8 : ℝ) ≤ 2 * Real.log r := by linarith only [Real.log_nonneg hr₁]
  have he := shift_exp_upper (-(21 / 8)) 0.0558 (by decide +kernel) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat, Rat.cast_ofScientific] at he
  have he' : Real.exp ((11 / 10 : ℝ) * -(21 / 8)) ≤ 0.0558 := by
    norm_num only
    exact he
  have hr₀ := zero_lt_one.trans_le hr₁
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound (N := 426) (j := 9) (n := 27) (lo := 5) (hi := 6.055)
        (by decide +kernel)).2
  simp only [Rat.cast_ofScientific] at hlog
  have hcap : 2 * Real.log r ≤ 12.11 := cap_log_bound hr₀ hr.2 (by linarith only [hlog])
  refine (cap_rectangle_354 hr₀ hh he' hcap (cap_decay_328 hr.1)).trans ?_
  norm_num only [momentBox, Analysis.logPowerTailPoly, Finset.sum_range_succ, Finset.sum_range_zero,
    Nat.choose, Nat.reduceAdd, Nat.reduceSub, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]

private theorem k197_reflect_to426 {r : ℝ} (hr : r ∈ Set.Icc 328 426) :
    14.21 ≤ 21 / 8 + Real.log (r ^ 2) ∧
      0.000000091 ≤ Real.exp (-(11 / 10) * (21 / 8 + Real.log (r ^ 2))) := by
  have h₀ := (by norm_num only : (0 : ℝ) < 328).trans_le hr.1
  have hl :=
    (Analysis.rationalLogIntervalCheck_sound (N := 328) (j := 9) (n := 27) (lo := 5.793) (hi := 6)
        (by decide +kernel)).1
  have hu :=
    (Analysis.rationalLogIntervalCheck_sound (N := 426) (j := 9) (n := 27) (lo := 5) (hi := 6.055)
        (by decide +kernel)).2
  have he :=
    (Analysis.rationalLogIntervalCheck_sound (N := 1000000000 / 91) (j := 23) (n := 32) (lo :=
        16.2124) (hi := 17) (by decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div, Rat.cast_ofScientific] at hl hu he
  have hz : 14.21 ≤ 21 / 8 + Real.log (r ^ 2) := by
    rw [Real.log_pow]
    linarith only [hl, Real.log_le_log (by norm_num only : (0 : ℝ) < 328) hr.1]
  have hru : r ≤ (426 : ℝ) := by linarith only [hr.2]
  have hd : 0.000000091 ≤ Real.exp (-(11 / 10) * (21 / 8 + Real.log (r ^ 2))) := by
    apply (Real.log_le_iff_le_exp (by norm_num only)).mp
    have hi : Real.log (0.000000091 : ℝ)⁻¹ ≥ 16.2124 := by
      norm_num only at he ⊢; exact he
    rw [Real.log_inv] at hi
    rw [Real.log_pow]
    linarith only [hi, hu, Real.log_le_log h₀ hru]
  exact ⟨hz, hd⟩

/-- The prefix through 2701 gives a uniform lower bound for three copies
of the principal reflected Euler series through radius 426. -/
theorem gaussian_k197_reflect_credit_to426 {r : ℝ} (hr : r ∈ Set.Icc 328 426) :
    0.0054 ≤ 3 * quarterMainEuler656 (1 : DirichletCharacter ℂ 1) (r ^ 2) := by
  obtain ⟨hz, hd⟩ := k197_reflect_to426 hr
  exact reflect_credit_of_exp hr.1 hz hd (by norm_num only)

private theorem first_rectangle_to426 {z : ℝ} (hl : 14.232 ≤ z) (hu : z ≤ 14.735) :
    0.0182 ≤ quarterGammaFirst656 z := by
  have ht :=
    (Analysis.rationalLogIntervalCheck_sound (N := 1000000 / 196) (j := 13) (n := 48) (lo := 8)
        (hi := 8.538) (by decide +kernel)).2
  have hf :=
    (Analysis.rationalLogIntervalCheck_sound (N := 1000000 / 631) (j := 11) (n := 48) (lo := 7.3682)
        (hi := 8) (by decide +kernel)).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at ht hf
  have htail : Real.exp (-(3 / 5 : ℝ) * 14.232) ≤ 0.000196 := by
    rw [neg_mul]
    apply exp_neg_le_of_log_inv (by norm_num only)
    norm_num only at ht ⊢
    linarith only [ht]
  have hfront : 0.000631 ≤ Real.exp (-(1 / 2 : ℝ) * 14.735) := by
    rw [neg_mul]
    apply le_exp_neg_of_log_inv (by norm_num only)
    norm_num only at hf ⊢
    linarith only [hf]
  have hm :=
    first_moment_lower_of_exp htail (m := 2194)
      (by norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat, Nat.cast_one])
      (by norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat, Nat.cast_one])
  exact
    first_rectangle_lower (c := 0.0182) (by norm_num only) hl hu hfront hm (by norm_num only)
      (by norm_num only)

/-- The first Gamma pole gives a uniform credit for radii between 663/2
and 426, covering the middle K197 radii. -/
theorem quarter_gamma_k197_to426 {r : ℝ} (hr : r ∈ Set.Icc (663 / 2) 426) :
    (centralGammaPair656 (1 : DirichletCharacter ℂ 1) (r ^ 2)).re ≤
      -2.16 * quarterWeight656 (r ^ 2) 1 - 0.0182 := by
  have hl :=
    (Analysis.rationalLogIntervalCheck_sound (N := 663 / 2) (j := 9) (n := 32) (lo := 5.8035) (hi :=
        6) (by decide +kernel)).1
  have hu :=
    (Analysis.rationalLogIntervalCheck_sound (N := 426) (j := 9) (n := 32) (lo := 5) (hi := 6.055)
        (by decide +kernel)).2
  simp only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hl hu
  have hr₀ : 0 < r := (by norm_num only : (0 : ℝ) < 663 / 2).trans_le hr.1
  have hlo := Real.log_le_log (by norm_num only : (0 : ℝ) < 663 / 2) hr.1
  have hup := Real.log_le_log hr₀ hr.2
  have hfirst : 0.0182 ≤ quarterGammaFirst656 (Real.log (r ^ 2) + 21 / 8) := by
    rw [Real.log_pow]
    exact first_rectangle_to426 (by linarith only [hl, hlo]) (by linarith only [hu, hup])
  exact
    (quarter_principal_gamma_upper_656 ((by norm_num only : (322 : ℝ) ≤ 663 / 2).trans hr.1)).trans
      (sub_le_sub_left hfirst _)

private theorem k197_log_credit_to426 {r : ℝ} (hr : r ∈ Set.Icc (663 / 2) 426) :
    0.0016 ≤ 4 * quarterWeight656 (r ^ 2) (r ^ 2) * Real.log (2 * Real.pi) := by
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
      ((by norm_num only : (0 : ℝ) ≤ 0.09319731 / 426).trans hw)
  linarith only [h]

/-- On the middle K197 radii through 426, any certified signed boundary
cost gives a principal-sum lower bound including the Gamma term. -/
theorem gaussian_k197_principal_to426 (hRH : RiemannHypothesis) {r B : ℝ}
    (hr : r ∈ Set.Icc (663 / 2) 426)
    (hb : -4 * (Chebyshev.psi (r ^ 2) - r ^ 2) * quarterWeight656 (r ^ 2) (r ^ 2) ≤ B) :
    let x := r ^ 2
    let W := fun n ↦ (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) x n).re
    (0.71780481 : ℝ) * r + 0.029188 - B <
      4 * (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, W n) - (∑' n, W n) -
        3 * (centralGammaPair656 (1 : DirichletCharacter ℂ 1) x).re := by
  intro x W
  have h :=
    gaussian_principal_gamma_lower hRH ((by norm_num only : (331 : ℝ) ≤ 663 / 2).trans hr.1)
      (quarter_gamma_k197_to426 hr) hb (k197_log_credit_to426 hr)
  dsimp only [x, W] at h ⊢
  linarith only [h]

private theorem conductor_endpoint_box {r z p C : ℝ} (hr : 1 ≤ r) (hz : 2 * Real.log r ≤ z)
    (hp : r ^ (-(6 / 5) : ℝ) ≤ p)
    (hb : (11 / 10 : ℝ) ^ 5 / 30 * p * (0.055715328 * (z + 21 / 8) ^ 5) ≤ C) :
    4 * r * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ C := by
  have hlog : 0 ≤ 2 * Real.log r + 21 / 8 := by linarith only [Real.log_nonneg hr]
  have hv : 2 * Real.log r + 21 / 8 ≤ z + 21 / 8 := by linarith only [hz]
  have hpoly :=
    mul_le_mul main_conductor_exp_656 (pow_le_pow_left₀ hlog hv 5) (pow_nonneg hlog _)
      (by norm_num only)
  have hmul :=
    mul_le_mul hp hpoly (mul_nonneg (Real.exp_pos _).le (pow_nonneg hlog _))
      ((Real.rpow_nonneg (zero_le_one.trans hr) _).trans hp)
  rw [main_conductor_factor_656 hr]
  nlinarith only [hmul, hb]

private theorem radius_log_3943 : Real.log (3943 / 10 : ℝ) ∈ Set.Icc 5.97711 5.97712 := by
  have h :=
    Analysis.rationalLogIntervalCheck_sound (N := 3943 / 10) (j := 9) (n := 27) (lo := 5.97711)
      (hi := 5.97712) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at h ⊢
  exact h

private theorem radius_power_3943 : (3943 / 10 : ℝ) ^ (-(6 / 5) : ℝ) ≤ 0.000767377 := by
  have h :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 3943 / 10) (p := 6)
        (d := 5) (lo := 0) (hi := 0.000767377) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat,
    neg_div] at h ⊢
  exact h

/-- The shifted conductor term is at least -2.68240 at radii from 3943 / 10. -/
theorem theta_from3943 {r : ℝ} (hr : (3943 / 10 : ℝ) ≤ r) :
    (-2.68240 : ℝ) ≤ gaussianTheta197 r := by
  have hlog : (23 / 2 : ℝ) ≤ 2 * Real.log (3943 / 10) := by linarith only [radius_log_3943.1]
  have hP :=
    conductor_poly_mono (sub_nonneg.mpr hlog) (by norm_num only : (0 : ℝ) ≤ 0.45424)
      (show 2 * Real.log (3943 / 10) - 23 / 2 ≤ 0.45424 by linarith only [radius_log_3943.2])
  have hprod :=
    (mul_le_mul_of_nonneg_left hP (Real.rpow_nonneg (by norm_num only) _)).trans
      (mul_le_mul_of_nonneg_right radius_power_3943 (by norm_num only [gaussianConductorPoly197]))
  apply gaussian_theta_endpoint_197 (by norm_num only) hr hlog
  rw [mul_assoc]
  exact
    (mul_le_mul_of_nonneg_left hprod (by norm_num only : (0 : ℝ) ≤ (11 / 10) ^ 5 / 30)).trans
      (by norm_num only [gaussianConductorPoly197])

/-- The principal inverse-scale conductor is bounded by its certified
value at radius 3943 / 10 for all larger radii. -/
theorem quarter_main_conductor_from3943 {r : ℝ} (hr : (3943 / 10 : ℝ) ≤ r) :
    4 * r * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 1.51183 := by
  have hb :=
    conductor_endpoint_box (r := 3943 / 10) (z := 11.95424) (C := 1.51183) (by norm_num only)
      (by linarith only [radius_log_3943.2]) radius_power_3943 (by norm_num only)
  have hl : (3943 / 10 : ℝ) ∈ Set.Ici 328 := by norm_num only [Set.mem_Ici]
  have he := main_conductor_antitone hl (hl.trans hr) hr
  exact he.trans hb

/-- The inverse-scale principal conductor is at most 1.50222 after
division by a Gaussian scale of at least 1.0064. -/
theorem gaussian_main_conductor_from3943 {r s : ℝ} (hr : (3943 / 10 : ℝ) ≤ r) (hs : 1.0064 ≤ s) :
    4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 1.50222 := by
  have hs₀ : 0 < s := (by norm_num only : (0 : ℝ) < 1.0064).trans_le hs
  rw [show
      4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re =
        (4 * r * (quarterKernel656.transform (r ^ 2)⁻¹).re) / s
      by ring]
  apply (div_le_iff₀ hs₀).mpr
  linarith only [quarter_main_conductor_from3943 hr, hs]

private theorem radius_log_4089 : Real.log (4089 / 10 : ℝ) ∈ Set.Icc 6.01347 6.01348 := by
  have h :=
    Analysis.rationalLogIntervalCheck_sound (N := 4089 / 10) (j := 9) (n := 27) (lo := 6.01347)
      (hi := 6.01348) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at h ⊢
  exact h

private theorem radius_power_4089 : (4089 / 10 : ℝ) ^ (-(6 / 5) : ℝ) ≤ 0.000734616 := by
  have h :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 4089 / 10) (p := 6)
        (d := 5) (lo := 0) (hi := 0.000734616) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat,
    neg_div] at h ⊢
  exact h

/-- The shifted conductor term is at least -2.62498 at radii from 4089 / 10. -/
theorem theta_from4089 {r : ℝ} (hr : (4089 / 10 : ℝ) ≤ r) :
    (-2.62498 : ℝ) ≤ gaussianTheta197 r := by
  have hlog : (23 / 2 : ℝ) ≤ 2 * Real.log (4089 / 10) := by linarith only [radius_log_4089.1]
  have hP :=
    conductor_poly_mono (sub_nonneg.mpr hlog) (by norm_num only : (0 : ℝ) ≤ 0.52696)
      (show 2 * Real.log (4089 / 10) - 23 / 2 ≤ 0.52696 by linarith only [radius_log_4089.2])
  have hprod :=
    (mul_le_mul_of_nonneg_left hP (Real.rpow_nonneg (by norm_num only) _)).trans
      (mul_le_mul_of_nonneg_right radius_power_4089 (by norm_num only [gaussianConductorPoly197]))
  apply gaussian_theta_endpoint_197 (by norm_num only) hr hlog
  rw [mul_assoc]
  exact
    (mul_le_mul_of_nonneg_left hprod (by norm_num only : (0 : ℝ) ≤ (11 / 10) ^ 5 / 30)).trans
      (by norm_num only [gaussianConductorPoly197])

/-- The principal inverse-scale conductor is bounded by its certified
value at radius 4089 / 10 for all larger radii. -/
theorem quarter_main_conductor_from4089 {r : ℝ} (hr : (4089 / 10 : ℝ) ≤ r) :
    4 * r * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 1.48374 := by
  have hb :=
    conductor_endpoint_box (r := 4089 / 10) (z := 12.02696) (C := 1.48374) (by norm_num only)
      (by linarith only [radius_log_4089.2]) radius_power_4089 (by norm_num only)
  have hl : (4089 / 10 : ℝ) ∈ Set.Ici 328 := by norm_num only [Set.mem_Ici]
  have he := main_conductor_antitone hl (hl.trans hr) hr
  exact he.trans hb

/-- The inverse-scale principal conductor is at most 1.47431 after
division by a Gaussian scale of at least 1.0064. -/
theorem gaussian_main_conductor_from4089 {r s : ℝ} (hr : (4089 / 10 : ℝ) ≤ r) (hs : 1.0064 ≤ s) :
    4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 1.47431 := by
  have hs₀ : 0 < s := (by norm_num only : (0 : ℝ) < 1.0064).trans_le hs
  rw [show
      4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re =
        (4 * r * (quarterKernel656.transform (r ^ 2)⁻¹).re) / s
      by ring]
  apply (div_le_iff₀ hs₀).mpr
  linarith only [quarter_main_conductor_from4089 hr, hs]

end PseudoPrime.PrimeTestBounds.MillerRabin
