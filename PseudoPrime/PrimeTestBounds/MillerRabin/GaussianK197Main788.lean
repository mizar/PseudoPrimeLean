/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Main672
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

/-! # Principal and reflected bounds for K197 through radius 788 -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For radii from 332.15 to 788, the combined K197 reflection
is at least -0.000791 by the common endpoint moment estimate. -/
theorem gaussian_joint_to788 (hRH : RiemannHypothesis) {r : ℝ} (hr : r ∈ Set.Icc 332.15 788)
    (α : ℕ → ℝ) (hα : ∀ n, 0 ≤ α n ∧ α n ≤ 4)
    (hprefix : ∀ n : ℕ, (n : ℝ) ≤ r ^ 2 → ArithmeticFunction.vonMangoldt n ≠ 0 → α n = 0) :
    (-0.000791 : ℝ) ≤
      ∑ i, (gaussianCoeff197 i : ℝ) * quarterAuxReflection656 α r (quarterShift663 i : ℝ) := by
  have hhi :=
    (Analysis.rationalLogIntervalCheck_sound (N := 788) (j := 9) (n := 27) (lo := 5) (hi := 6.67)
        (by decide +kernel)).2
  norm_num only [Rat.cast_ofScientific] at hhi
  have hrU : r ≤ (788 : ℝ) := by linarith only [hr.2]
  have hl := (Real.log_le_log ((by norm_num only : (0 : ℝ) < 332.15).trans_le hr.1) hrU).trans hhi
  have h :=
    joint_lower_box hRH (u := 15.18) (L := 13.34) (E := 0.000791)
      ⟨hr.1, hr.2.trans (by norm_num only)⟩
      (by
        norm_num only [Rat.cast_ofScientific]; linarith only [hl])
      (by norm_num only [Rat.cast_ofScientific]) (by decide +kernel) α hα hprefix
  norm_num only [Rat.cast_ofScientific] at h ⊢
  exact h

/-- The main reflected kernel costs at most 0.001 on radii 328 through 788. -/
theorem k197_main_reflect_to788 {r : ℝ} (hr : r ∈ Set.Icc 328 788) :
    quarterAuxReflectCap656 r (-(21 / 8)) 103684 ≤ 0.001 := by
  have hr₁ : (1 : ℝ) ≤ r := (by norm_num only : (1 : ℝ) ≤ 328).trans hr.1
  have hh : -(21 / 8 : ℝ) ≤ 2 * Real.log r := by linarith only [Real.log_nonneg hr₁]
  have he := shift_exp_upper (-(21 / 8)) 0.0558 (by decide +kernel) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat, Rat.cast_ofScientific] at he
  have he' : Real.exp ((11 / 10 : ℝ) * -(21 / 8)) ≤ 0.0558 := by
    norm_num only
    exact he
  have hr₀ := zero_lt_one.trans_le hr₁
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound (N := 788) (j := 9) (n := 27) (lo := 5) (hi := 6.67)
        (by decide +kernel)).2
  simp only [Rat.cast_ofScientific] at hlog
  have hcap : 2 * Real.log r ≤ 13.34 := cap_log_bound hr₀ hr.2 (by linarith only [hlog])
  refine (cap_rectangle_354 hr₀ hh he' hcap (cap_decay_328 hr.1)).trans ?_
  norm_num only [momentBox, Analysis.logPowerTailPoly, Finset.sum_range_succ, Finset.sum_range_zero,
    Nat.choose, Nat.reduceAdd, Nat.reduceSub, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]

private theorem k197_reflect_to788 {r : ℝ} (hr : r ∈ Set.Icc 328 788) :
    14.21 ≤ 21 / 8 + Real.log (r ^ 2) ∧
      0.000000023 ≤ Real.exp (-(11 / 10) * (21 / 8 + Real.log (r ^ 2))) := by
  have h₀ := (by norm_num only : (0 : ℝ) < 328).trans_le hr.1
  have hl :=
    (Analysis.rationalLogIntervalCheck_sound (N := 328) (j := 9) (n := 27) (lo := 5.793) (hi := 6)
        (by decide +kernel)).1
  have hu :=
    (Analysis.rationalLogIntervalCheck_sound (N := 788) (j := 9) (n := 27) (lo := 5) (hi := 6.67)
        (by decide +kernel)).2
  have he :=
    (Analysis.rationalLogIntervalCheck_sound (N := 1000000000 / 23) (j := 25) (n := 32) (lo :=
        17.5877) (hi := 18) (by decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div, Rat.cast_ofScientific] at hl hu he
  have hz : 14.21 ≤ 21 / 8 + Real.log (r ^ 2) := by
    rw [Real.log_pow]
    linarith only [hl, Real.log_le_log (by norm_num only : (0 : ℝ) < 328) hr.1]
  have hru : r ≤ (788 : ℝ) := by linarith only [hr.2]
  have hd : 0.000000023 ≤ Real.exp (-(11 / 10) * (21 / 8 + Real.log (r ^ 2))) := by
    apply (Real.log_le_iff_le_exp (by norm_num only)).mp
    have hi : Real.log (0.000000023 : ℝ)⁻¹ ≥ 17.5877 := by
      norm_num only at he ⊢; exact he
    rw [Real.log_inv] at hi
    rw [Real.log_pow]
    linarith only [hi, hu, Real.log_le_log h₀ hru]
  exact ⟨hz, hd⟩

/-- The prefix through 2701 gives a uniform lower bound for three copies
of the principal reflected Euler series through radius 788. -/
theorem gaussian_k197_reflect_credit_to788 {r : ℝ} (hr : r ∈ Set.Icc 328 788) :
    0.00137 ≤ 3 * quarterMainEuler656 (1 : DirichletCharacter ℂ 1) (r ^ 2) := by
  obtain ⟨hz, hd⟩ := k197_reflect_to788 hr
  exact reflect_credit_of_exp hr.1 hz hd (by norm_num only)

private theorem first_rectangle_to788 {z : ℝ} (hl : 14.232 ≤ z) (hu : z ≤ 15.965) :
    0.0096 ≤ quarterGammaFirst656 z := by
  have ht :=
    (Analysis.rationalLogIntervalCheck_sound (N := 1000000 / 196) (j := 13) (n := 48) (lo := 8)
        (hi := 8.538) (by decide +kernel)).2
  have hf :=
    (Analysis.rationalLogIntervalCheck_sound (N := 1000000 / 340) (j := 11) (n := 48) (lo := 7.9865)
        (hi := 8) (by decide +kernel)).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at ht hf
  have htail : Real.exp (-(3 / 5 : ℝ) * 14.232) ≤ 0.000196 := by
    rw [neg_mul]
    apply exp_neg_le_of_log_inv (by norm_num only)
    norm_num only at ht ⊢
    linarith only [ht]
  have hfront : 0.000340 ≤ Real.exp (-(1 / 2 : ℝ) * 15.965) := by
    rw [neg_mul]
    apply le_exp_neg_of_log_inv (by norm_num only)
    norm_num only at hf ⊢
    linarith only [hf]
  have hm :=
    first_moment_lower_of_exp htail (m := 2194)
      (by norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat, Nat.cast_one])
      (by norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat, Nat.cast_one])
  exact
    first_rectangle_lower (c := 0.0096) (by norm_num only) hl hu hfront hm (by norm_num only)
      (by norm_num only)

/-- The first Gamma pole gives a uniform credit for radii between 663/2
and 788, covering the middle K197 radii. -/
theorem quarter_gamma_k197_to788 {r : ℝ} (hr : r ∈ Set.Icc (663 / 2) 788) :
    (centralGammaPair656 (1 : DirichletCharacter ℂ 1) (r ^ 2)).re ≤
      -2.16 * quarterWeight656 (r ^ 2) 1 - 0.0096 := by
  have hl :=
    (Analysis.rationalLogIntervalCheck_sound (N := 663 / 2) (j := 9) (n := 32) (lo := 5.8035) (hi :=
        6) (by decide +kernel)).1
  have hu :=
    (Analysis.rationalLogIntervalCheck_sound (N := 788) (j := 9) (n := 32) (lo := 5) (hi := 6.67)
        (by decide +kernel)).2
  simp only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hl hu
  have hr₀ : 0 < r := (by norm_num only : (0 : ℝ) < 663 / 2).trans_le hr.1
  have hlo := Real.log_le_log (by norm_num only : (0 : ℝ) < 663 / 2) hr.1
  have hup := Real.log_le_log hr₀ hr.2
  have hfirst : 0.0096 ≤ quarterGammaFirst656 (Real.log (r ^ 2) + 21 / 8) := by
    rw [Real.log_pow]
    exact first_rectangle_to788 (by linarith only [hl, hlo]) (by linarith only [hu, hup])
  exact
    (quarter_principal_gamma_upper_656 ((by norm_num only : (322 : ℝ) ≤ 663 / 2).trans hr.1)).trans
      (sub_le_sub_left hfirst _)

private theorem k197_log_credit_to788 {r : ℝ} (hr : r ∈ Set.Icc (663 / 2) 788) :
    0.00086 ≤ 4 * quarterWeight656 (r ^ 2) (r ^ 2) * Real.log (2 * Real.pi) := by
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
      ((by norm_num only : (0 : ℝ) ≤ 0.09319731 / 788).trans hw)
  linarith only [h]

/-- On the middle K197 radii through 788, any certified signed boundary
cost gives a principal-sum lower bound including the Gamma term. -/
theorem gaussian_k197_principal_to788 (hRH : RiemannHypothesis) {r B : ℝ}
    (hr : r ∈ Set.Icc (663 / 2) 788)
    (hb : -4 * (Chebyshev.psi (r ^ 2) - r ^ 2) * quarterWeight656 (r ^ 2) (r ^ 2) ≤ B) :
    let x := r ^ 2
    let W := fun n ↦ (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) x n).re
    (0.71780481 : ℝ) * r + 0.002648 - B <
      4 * (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, W n) - (∑' n, W n) -
        3 * (centralGammaPair656 (1 : DirichletCharacter ℂ 1) x).re := by
  intro x W
  have h :=
    gaussian_principal_gamma_lower hRH ((by norm_num only : (331 : ℝ) ≤ 663 / 2).trans hr.1)
      (quarter_gamma_k197_to788 hr) hb (k197_log_credit_to788 hr)
  dsimp only [x, W] at h ⊢
  linarith only [h]

private theorem conductors_from_endpoint {a r s p z T C N : ℝ} (ha : 328 ≤ a) (hr : a ≤ r)
    (hs : 1.02 ≤ s) (hlo : (23 / 2 : ℝ) ≤ 2 * Real.log a) (hhi : 2 * Real.log a ≤ z)
    (hp : a ^ (-(6 / 5) : ℝ) ≤ p)
    (hT : (11 / 10 : ℝ) ^ 5 / 30 * p * gaussianConductorPoly197 (z - 23 / 2) ≤ T)
    (hC : (11 / 10 : ℝ) ^ 5 / 30 * p * (0.055715328 * (z + 21 / 8) ^ 5) ≤ C) (hN : 0 ≤ N)
    (hCN : C ≤ N * 1.02) :
    -T ≤ gaussianTheta197 r ∧ 4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ N := by
  have ha₀ : 0 < a := (by norm_num only : (0 : ℝ) < 328).trans_le ha
  have hs₀ : 0 < s := (by norm_num only : (0 : ℝ) < 1.02).trans_le hs
  have hpoly :=
    conductor_poly_mono (sub_nonneg.mpr hlo) (sub_nonneg.mpr (hlo.trans hhi))
      (sub_le_sub_right hhi (23 / 2))
  have hnon :=
    conductor_poly_mono (by norm_num only : (0 : ℝ) ≤ 0) (sub_nonneg.mpr hlo) (sub_nonneg.mpr hlo)
  have hpoly₀ : 0 ≤ gaussianConductorPoly197 (2 * Real.log a - 23 / 2) :=
    (by norm_num only [gaussianConductorPoly197] : (0 : ℝ) ≤ gaussianConductorPoly197 0).trans hnon
  have hmul := mul_le_mul hp hpoly hpoly₀ ((Real.rpow_nonneg ha₀.le _).trans hp)
  have ht := (mul_le_mul_of_nonneg_left hmul (by norm_num only : (0 : ℝ) ≤ (11 / 10) ^ 5 / 30))
  refine ⟨gaussian_theta_endpoint_197 ha₀ hr hlo ?_, ?_⟩
  · linarith only [ht, hT]
  have hb := conductor_endpoint_box ((by norm_num only : (1 : ℝ) ≤ 328).trans ha) hhi hp hC
  have hc := (main_conductor_antitone ha (ha.trans hr) hr).trans hb
  rw [show
      4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re =
        (4 * r * (quarterKernel656.transform (r ^ 2)⁻¹).re) / s
      by ring]
  exact (div_le_iff₀ hs₀).mpr (hc.trans (hCN.trans (mul_le_mul_of_nonneg_left hs hN)))

/-- At radii from 671, bound the two K197 conductor terms
using the certified endpoint and the scale floor 1.02. -/
theorem conductors_from6710 {r s : ℝ} (hr : (6710 / 10 : ℝ) ≤ r) (hs : 1.02 ≤ s) :
    -1.898194 ≤ gaussianTheta197 r ∧
      4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 1.113502 := by
  have hl :=
    Analysis.rationalLogIntervalCheck_sound (N := 6710 / 10) (j := 10) (n := 27) (lo := 6.50875)
      (hi := 6.50878) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hl
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 6710 / 10) (p := 6)
        (d := 5) (lo := 0) (hi := 0.000405447) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat, neg_div] at hp
  norm_num only at hr
  exact
    conductors_from_endpoint (z := 13.01756) (C := 1.135771) (by norm_num only) hr hs
      (by linarith only [hl.1]) (by linarith only [hl.2]) hp
      (by norm_num only [gaussianConductorPoly197]) (by norm_num only) (by norm_num only)
      (by norm_num only)

/-- At radii from 679.3, bound the two K197 conductor terms
using the certified endpoint and the scale floor 1.02. -/
theorem conductors_from6793 {r s : ℝ} (hr : (6793 / 10 : ℝ) ≤ r) (hs : 1.02 ≤ s) :
    -1.881876 ≤ gaussianTheta197 r ∧
      4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 1.105851 := by
  have hl :=
    Analysis.rationalLogIntervalCheck_sound (N := 6793 / 10) (j := 10) (n := 27) (lo := 6.52105)
      (hi := 6.52108) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hl
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 6793 / 10) (p := 6)
        (d := 5) (lo := 0) (hi := 0.00039951) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat, neg_div] at hp
  norm_num only at hr
  exact
    conductors_from_endpoint (z := 13.04216) (C := 1.127967) (by norm_num only) hr hs
      (by linarith only [hl.1]) (by linarith only [hl.2]) hp
      (by norm_num only [gaussianConductorPoly197]) (by norm_num only) (by norm_num only)
      (by norm_num only)

/-- At radii from 687.7, bound the two K197 conductor terms
using the certified endpoint and the scale floor 1.02. -/
theorem conductors_from6877 {r s : ℝ} (hr : (6877 / 10 : ℝ) ≤ r) (hs : 1.02 ≤ s) :
    -1.865649 ≤ gaussianTheta197 r ∧
      4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 1.098236 := by
  have hl :=
    Analysis.rationalLogIntervalCheck_sound (N := 6877 / 10) (j := 10) (n := 27) (lo := 6.53334)
      (hi := 6.53337) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hl
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 6877 / 10) (p := 6)
        (d := 5) (lo := 0) (hi := 0.000393661) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat, neg_div] at hp
  norm_num only at hr
  exact
    conductors_from_endpoint (z := 13.06674) (C := 1.120199) (by norm_num only) hr hs
      (by linarith only [hl.1]) (by linarith only [hl.2]) hp
      (by norm_num only [gaussianConductorPoly197]) (by norm_num only) (by norm_num only)
      (by norm_num only)

/-- At radii from 695.8, bound the two K197 conductor terms
using the certified endpoint and the scale floor 1.02. -/
theorem conductors_from6958 {r s : ℝ} (hr : (6958 / 10 : ℝ) ≤ r) (hs : 1.02 ≤ s) :
    -1.850282 ≤ gaussianTheta197 r ∧
      4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 1.09102 := by
  have hl :=
    Analysis.rationalLogIntervalCheck_sound (N := 6958 / 10) (j := 10) (n := 27) (lo := 6.54505)
      (hi := 6.54508) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hl
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 6958 / 10) (p := 6)
        (d := 5) (lo := 0) (hi := 0.000388169) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat, neg_div] at hp
  norm_num only at hr
  exact
    conductors_from_endpoint (z := 13.09016) (C := 1.112839) (by norm_num only) hr hs
      (by linarith only [hl.1]) (by linarith only [hl.2]) hp
      (by norm_num only [gaussianConductorPoly197]) (by norm_num only) (by norm_num only)
      (by norm_num only)

/-- At radii from 704.3, bound the two K197 conductor terms
using the certified endpoint and the scale floor 1.02. -/
theorem conductors_from7043 {r s : ℝ} (hr : (7043 / 10 : ℝ) ≤ r) (hs : 1.02 ≤ s) :
    -1.834431 ≤ gaussianTheta197 r ∧
      4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 1.08357 := by
  have hl :=
    Analysis.rationalLogIntervalCheck_sound (N := 7043 / 10) (j := 10) (n := 27) (lo := 6.55719)
      (hi := 6.55722) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hl
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 7043 / 10) (p := 6)
        (d := 5) (lo := 0) (hi := 0.000382554) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat, neg_div] at hp
  norm_num only at hr
  exact
    conductors_from_endpoint (z := 13.11444) (C := 1.10524) (by norm_num only) hr hs
      (by linarith only [hl.1]) (by linarith only [hl.2]) hp
      (by norm_num only [gaussianConductorPoly197]) (by norm_num only) (by norm_num only)
      (by norm_num only)

/-- At radii from 712.5, bound the two K197 conductor terms
using the certified endpoint and the scale floor 1.02. -/
theorem conductors_from7125 {r s : ℝ} (hr : (7125 / 10 : ℝ) ≤ r) (hs : 1.02 ≤ s) :
    -1.819406 ≤ gaussianTheta197 r ∧
      4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 1.076501 := by
  have hl :=
    Analysis.rationalLogIntervalCheck_sound (N := 7125 / 10) (j := 10) (n := 27) (lo := 6.56876)
      (hi := 6.56879) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hl
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 7125 / 10) (p := 6)
        (d := 5) (lo := 0) (hi := 0.000377277) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat, neg_div] at hp
  norm_num only at hr
  exact
    conductors_from_endpoint (z := 13.13758) (C := 1.09803) (by norm_num only) hr hs
      (by linarith only [hl.1]) (by linarith only [hl.2]) hp
      (by norm_num only [gaussianConductorPoly197]) (by norm_num only) (by norm_num only)
      (by norm_num only)

/-- At radii from 721, bound the two K197 conductor terms
using the certified endpoint and the scale floor 1.02. -/
theorem conductors_from7210 {r s : ℝ} (hr : (7210 / 10 : ℝ) ≤ r) (hs : 1.02 ≤ s) :
    -1.804106 ≤ gaussianTheta197 r ∧
      4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 1.0693 := by
  have hl :=
    Analysis.rationalLogIntervalCheck_sound (N := 7210 / 10) (j := 10) (n := 27) (lo := 6.58062)
      (hi := 6.58065) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hl
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 7210 / 10) (p := 6)
        (d := 5) (lo := 0) (hi := 0.000371946) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat, neg_div] at hp
  norm_num only at hr
  exact
    conductors_from_endpoint (z := 13.1613) (C := 1.090684) (by norm_num only) hr hs
      (by linarith only [hl.1]) (by linarith only [hl.2]) hp
      (by norm_num only [gaussianConductorPoly197]) (by norm_num only) (by norm_num only)
      (by norm_num only)

/-- At radii from 729.1, bound the two K197 conductor terms
using the certified endpoint and the scale floor 1.02. -/
theorem conductors_from7291 {r s : ℝ} (hr : (7291 / 10 : ℝ) ≤ r) (hs : 1.02 ≤ s) :
    -1.789782 ≤ gaussianTheta197 r ∧
      4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 1.062553 := by
  have hl :=
    Analysis.rationalLogIntervalCheck_sound (N := 7291 / 10) (j := 10) (n := 27) (lo := 6.5918)
      (hi := 6.59183) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hl
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 7291 / 10) (p := 6)
        (d := 5) (lo := 0) (hi := 0.000366993) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat, neg_div] at hp
  norm_num only at hr
  exact
    conductors_from_endpoint (z := 13.18366) (C := 1.083803) (by norm_num only) hr hs
      (by linarith only [hl.1]) (by linarith only [hl.2]) hp
      (by norm_num only [gaussianConductorPoly197]) (by norm_num only) (by norm_num only)
      (by norm_num only)

/-- At radii from 737.6, bound the two K197 conductor terms
using the certified endpoint and the scale floor 1.02. -/
theorem conductors_from7376 {r s : ℝ} (hr : (7376 / 10 : ℝ) ≤ r) (hs : 1.02 ≤ s) :
    -1.774992 ≤ gaussianTheta197 r ∧
      4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 1.05558 := by
  have hl :=
    Analysis.rationalLogIntervalCheck_sound (N := 7376 / 10) (j := 10) (n := 27) (lo := 6.60339)
      (hi := 6.60342) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hl
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 7376 / 10) (p := 6)
        (d := 5) (lo := 0) (hi := 0.000361923) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat, neg_div] at hp
  norm_num only at hr
  exact
    conductors_from_endpoint (z := 13.20684) (C := 1.07669) (by norm_num only) hr hs
      (by linarith only [hl.1]) (by linarith only [hl.2]) hp
      (by norm_num only [gaussianConductorPoly197]) (by norm_num only) (by norm_num only)
      (by norm_num only)

/-- At radii from 745.8, bound the two K197 conductor terms
using the certified endpoint and the scale floor 1.02. -/
theorem conductors_from7458 {r s : ℝ} (hr : (7458 / 10 : ℝ) ≤ r) (hs : 1.02 ≤ s) :
    -1.76097 ≤ gaussianTheta197 r ∧
      4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 1.048961 := by
  have hl :=
    Analysis.rationalLogIntervalCheck_sound (N := 7458 / 10) (j := 10) (n := 27) (lo := 6.61444)
      (hi := 6.61447) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hl
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 7458 / 10) (p := 6)
        (d := 5) (lo := 0) (hi := 0.000357154) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat, neg_div] at hp
  norm_num only at hr
  exact
    conductors_from_endpoint (z := 13.22894) (C := 1.069939) (by norm_num only) hr hs
      (by linarith only [hl.1]) (by linarith only [hl.2]) hp
      (by norm_num only [gaussianConductorPoly197]) (by norm_num only) (by norm_num only)
      (by norm_num only)

/-- At radii from 754.2, bound the two K197 conductor terms
using the certified endpoint and the scale floor 1.02. -/
theorem conductors_from7542 {r s : ℝ} (hr : (7542 / 10 : ℝ) ≤ r) (hs : 1.02 ≤ s) :
    -1.74684 ≤ gaussianTheta197 r ∧
      4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 1.042287 := by
  have hl :=
    Analysis.rationalLogIntervalCheck_sound (N := 7542 / 10) (j := 10) (n := 27) (lo := 6.62564)
      (hi := 6.62567) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hl
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 7542 / 10) (p := 6)
        (d := 5) (lo := 0) (hi := 0.000352385) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat, neg_div] at hp
  norm_num only at hr
  exact
    conductors_from_endpoint (z := 13.25134) (C := 1.063131) (by norm_num only) hr hs
      (by linarith only [hl.1]) (by linarith only [hl.2]) hp
      (by norm_num only [gaussianConductorPoly197]) (by norm_num only) (by norm_num only)
      (by norm_num only)

/-- At radii from 762.4, bound the two K197 conductor terms
using the certified endpoint and the scale floor 1.02. -/
theorem conductors_from7624 {r s : ℝ} (hr : (7624 / 10 : ℝ) ≤ r) (hs : 1.02 ≤ s) :
    -1.733286 ≤ gaussianTheta197 r ∧
      4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 1.035881 := by
  have hl :=
    Analysis.rationalLogIntervalCheck_sound (N := 7624 / 10) (j := 10) (n := 27) (lo := 6.63646)
      (hi := 6.63649) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hl
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 7624 / 10) (p := 6)
        (d := 5) (lo := 0) (hi := 0.000347842) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat, neg_div] at hp
  norm_num only at hr
  exact
    conductors_from_endpoint (z := 13.27298) (C := 1.056597) (by norm_num only) hr hs
      (by linarith only [hl.1]) (by linarith only [hl.2]) hp
      (by norm_num only [gaussianConductorPoly197]) (by norm_num only) (by norm_num only)
      (by norm_num only)

/-- At radii from 770.9, bound the two K197 conductor terms
using the certified endpoint and the scale floor 1.02. -/
theorem conductors_from7709 {r s : ℝ} (hr : (7709 / 10 : ℝ) ≤ r) (hs : 1.02 ≤ s) :
    -1.719456 ≤ gaussianTheta197 r ∧
      4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 1.029335 := by
  have hl :=
    Analysis.rationalLogIntervalCheck_sound (N := 7709 / 10) (j := 10) (n := 27) (lo := 6.64754)
      (hi := 6.64757) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hl
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 7709 / 10) (p := 6)
        (d := 5) (lo := 0) (hi := 0.000343245) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat, neg_div] at hp
  norm_num only at hr
  exact
    conductors_from_endpoint (z := 13.29514) (C := 1.04992) (by norm_num only) hr hs
      (by linarith only [hl.1]) (by linarith only [hl.2]) hp
      (by norm_num only [gaussianConductorPoly197]) (by norm_num only) (by norm_num only)
      (by norm_num only)

/-- At radii from 779.1, bound the two K197 conductor terms
using the certified endpoint and the scale floor 1.02. -/
theorem conductors_from7791 {r s : ℝ} (hr : (7791 / 10 : ℝ) ≤ r) (hs : 1.02 ≤ s) :
    -1.706335 ≤ gaussianTheta197 r ∧
      4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 1.023119 := by
  have hl :=
    Analysis.rationalLogIntervalCheck_sound (N := 7791 / 10) (j := 10) (n := 27) (lo := 6.65812)
      (hi := 6.65815) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hl
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 7791 / 10) (p := 6)
        (d := 5) (lo := 0) (hi := 0.000338914) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat, neg_div] at hp
  norm_num only at hr
  exact
    conductors_from_endpoint (z := 13.3163) (C := 1.04358) (by norm_num only) hr hs
      (by linarith only [hl.1]) (by linarith only [hl.2]) hp
      (by norm_num only [gaussianConductorPoly197]) (by norm_num only) (by norm_num only)
      (by norm_num only)

end PseudoPrime.PrimeTestBounds.MillerRabin
