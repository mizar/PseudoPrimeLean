/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Main1000
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Moments
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Main788
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

/-! # Principal and reflected bounds for K197 through radius 1165 -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private theorem joint_lower_late_box (hRH : RiemannHypothesis) {r : ℝ} {u L E : ℚ}
    (hr : r ∈ Set.Icc 995 1165) (hlu : Real.log r ≤ (L : ℝ) / 2)
    (hu : (2 * (L : ℝ) - 23 / 2) ≤ (u : ℝ))
    (hcert : 0 ≤ earlySum u L ∧ (4 * ((11 / 10 : ℚ) ^ 5 / 120 * 0.00000284)) * earlySum u L ≤ E)
    (α : ℕ → ℝ) (hα : ∀ n, 0 ≤ α n ∧ α n ≤ 4)
    (hprefix : ∀ n : ℕ, (n : ℝ) ≤ r ^ 2 → ArithmeticFunction.vonMangoldt n ≠ 0 → α n = 0) :
    -(E : ℝ) ≤
      ∑ i, (gaussianCoeff197 i : ℝ) * quarterAuxReflection656 α r (quarterShift663 i : ℝ) := by
  have hlow : (332.15 : ℝ) ≤ r := (by norm_num only : (332.15 : ℝ) ≤ 995).trans hr.1
  have hr₁ : 1 ≤ r := (by norm_num only : (1 : ℝ) ≤ 332.15).trans hlow
  have hx₀ := sq_pos_of_pos (zero_lt_one.trans_le hr₁)
  have hx := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 332.15) hlow 2
  have hx₁ : 1423 ≤ r ^ 2 := (by norm_num only : (1423 : ℝ) ≤ 332.15 ^ 2).trans hx
  have hlo :=
    (Analysis.rationalLogIntervalCheck_sound (N := 6643 / 20) (j := 9) (n := 27) (lo := 5.80555)
        (hi := 6) (by decide +kernel)).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hlo
  have hrl : (6643 / 20 : ℝ) ≤ r := by linarith only [hr.1]
  have hll := hlo.trans (Real.log_le_log (by norm_num only : (0 : ℝ) < 6643 / 20) hrl)
  have hlog : 4 * Real.log r - 23 / 2 ∈ Set.Icc (↑(11.722 : ℚ) : ℝ) (↑u : ℝ) := by
    norm_num only [Rat.cast_ofScientific, Set.mem_Icc]
    exact ⟨by linarith only [hll], by linarith only [hlu, hu]⟩
  have hL : 5 ≤ Real.log (r ^ 2) ∧ Real.log (r ^ 2) ≤ (L : ℝ) := by
    rw [Real.log_pow, Nat.cast_ofNat]
    exact ⟨by linarith only [hll], by linarith only [hlu]⟩
  have hbaseA :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := (6643 / 20) ^ 2) (p :=
        3) (d := 5) (lo := 0) (hi := 0.000943) (by decide +kernel)).2
  have hbaseB :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := (6643 / 20) ^ 2) (p :=
        11) (d := 10) (lo := 0) (hi := 0.00000284) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, Rat.cast_pow] at hbaseA hbaseB
  have hA : (r ^ 2) ^ (-(3 / 5) : ℝ) ≤ 0.000943 :=
    (Real.rpow_le_rpow_of_nonpos (by norm_num only : (0 : ℝ) < 332.15 ^ 2) hx
          (by norm_num only : (-(3 / 5) : ℝ) ≤ 0)).trans
      (by
        norm_num only; exact hbaseA)
  have hB : (r ^ 2) ^ (-(11 / 10) : ℝ) ≤ 0.00000284 :=
    (Real.rpow_le_rpow_of_nonpos (by norm_num only : (0 : ℝ) < 332.15 ^ 2) hx
          (by norm_num only : (-(11 / 10) : ℝ) ≤ 0)).trans
      (by
        norm_num only; exact hbaseB)
  have hD : -(Chebyshev.psi (r ^ 2) - r ^ 2) * (r ^ 2) ^ (-(8 / 5) : ℝ) ≤ 0.000002272 := by
    have hψ : |Chebyshev.psi (r ^ 2) - r ^ 2| ≤ Real.sqrt (r ^ 2) * (8.31 : ℝ) := by
      by_cases h : r ^ 2 ≤ 1000000
      · exact
          (AnalyticNumberTheory.Arithmetic.psi_four_fifths_1423_million hx₁ h).trans
            (by
              rw [mul_comm (4 / 5 : ℝ)]
              exact
                mul_le_mul_of_nonneg_left (by norm_num only : (4 / 5 : ℝ) ≤ 8.31)
                  (Real.sqrt_nonneg (r ^ 2)))
      have hbox : Real.log (r ^ 2) ≤ 14.122 := by
        rw [Real.log_pow, Nat.cast_ofNat]
        have hc :=
          (Analysis.rationalLogIntervalCheck_sound (N := 1165) (j := 10) (n := 27) (lo := 5) (hi :=
              7.061) (by decide +kernel)).2
        norm_num only [Rat.cast_ofScientific] at hc
        linarith only [hc, Real.log_le_log (zero_lt_one.trans_le hr₁) hr.2]
      have hs := pow_le_pow_left₀ ((by norm_num only : (0 : ℝ) ≤ 5).trans hL.1) hbox 2
      exact
        (euler570_psi_high hRH (le_of_not_ge h)).trans
          (mul_le_mul_of_nonneg_left (by linarith only [hs]) (Real.sqrt_nonneg _))
    have h :=
      mul_le_mul_of_nonneg_right ((neg_le_abs _).trans hψ) (Real.rpow_nonneg hx₀.le (-(8 / 5) : ℝ))
    have h995 := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 995) hr.1 2
    have hp :=
      (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := (995 : ℚ) ^ 2) (p :=
          11) (d := 10) (lo := 0) (hi := 0.000000256) (by decide +kernel)).2
    norm_num only [Rat.cast_pow, Rat.cast_ofNat, Rat.cast_ofScientific] at hp
    have hb' :=
      (Real.rpow_le_rpow_of_nonpos (by norm_num only : (0 : ℝ) < 995 ^ 2) h995
            (by norm_num only : (-(11 / 10) : ℝ) ≤ 0)).trans
        (by
          norm_num only; exact hp)
    have he : Real.sqrt (r ^ 2) * (r ^ 2) ^ (-(8 / 5) : ℝ) = (r ^ 2) ^ (-(11 / 10) : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx₀]
      norm_num only
    linarith only [h, he, hb']
  have hh := (Rat.cast_nonneg (K := ℝ)).mpr hcert.1
  rw [cast_earlySum] at hh
  have hj :=
    gaussian_joint_endpoint_197 hRH hr₁ hx₁ hL.1 (by norm_num only) hlog hA hB hL.2 hD hh α hα
      hprefix
  have hb := (Rat.cast_le (K := ℝ)).mpr hcert.2
  norm_num only [Rat.cast_mul, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat,
    Rat.cast_ofScientific] at hb
  rw [cast_earlySum] at hb
  linarith only [hj, hb]

/-- For radii from 995 to 1165, the combined K197 reflection
is at least -0.00145 by the common endpoint moment estimate. -/
theorem gaussian_joint_to1165 (hRH : RiemannHypothesis) {r : ℝ} (hr : r ∈ Set.Icc 995 1165)
    (α : ℕ → ℝ) (hα : ∀ n, 0 ≤ α n ∧ α n ≤ 4)
    (hprefix : ∀ n : ℕ, (n : ℝ) ≤ r ^ 2 → ArithmeticFunction.vonMangoldt n ≠ 0 → α n = 0) :
    (-0.00145 : ℝ) ≤
      ∑ i, (gaussianCoeff197 i : ℝ) * quarterAuxReflection656 α r (quarterShift663 i : ℝ) := by
  have hhi :=
    (Analysis.rationalLogIntervalCheck_sound (N := 1165) (j := 10) (n := 27) (lo := 5) (hi := 7.061)
        (by decide +kernel)).2
  norm_num only [Rat.cast_ofScientific] at hhi
  have hrU : r ≤ (1165 : ℝ) := by linarith only [hr.2]
  have hl := (Real.log_le_log ((by norm_num only : (0 : ℝ) < 995).trans_le hr.1) hrU).trans hhi
  have h :=
    joint_lower_late_box hRH (u := 16.744) (L := 14.122) (E := 0.00145) hr
      (by
        norm_num only [Rat.cast_ofScientific]; linarith only [hl])
      (by norm_num only [Rat.cast_ofScientific]) (by decide +kernel) α hα hprefix
  norm_num only [Rat.cast_ofScientific] at h ⊢
  exact h

/-- The main reflected kernel costs at most 0.0013 on radii 328 through 1165. -/
theorem k197_main_reflect_to1165 {r : ℝ} (hr : r ∈ Set.Icc 328 1165) :
    quarterAuxReflectCap656 r (-(21 / 8)) 103684 ≤ 0.0013 := by
  have hr₁ : (1 : ℝ) ≤ r := (by norm_num only : (1 : ℝ) ≤ 328).trans hr.1
  have hh : -(21 / 8 : ℝ) ≤ 2 * Real.log r := by linarith only [Real.log_nonneg hr₁]
  have he := shift_exp_upper (-(21 / 8)) 0.0558 (by decide +kernel) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat, Rat.cast_ofScientific] at he
  have he' : Real.exp ((11 / 10 : ℝ) * -(21 / 8)) ≤ 0.0558 := by
    norm_num only
    exact he
  have hr₀ := zero_lt_one.trans_le hr₁
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound (N := 1165) (j := 10) (n := 27) (lo := 5) (hi := 7.061)
        (by decide +kernel)).2
  simp only [Rat.cast_ofScientific] at hlog
  have hcap : 2 * Real.log r ≤ 14.122 := cap_log_bound hr₀ hr.2 (by linarith only [hlog])
  refine (cap_rectangle_354 hr₀ hh he' hcap (cap_decay_328 hr.1)).trans ?_
  norm_num only [momentBox, Analysis.logPowerTailPoly, Finset.sum_range_succ, Finset.sum_range_zero,
    Nat.choose, Nat.reduceAdd, Nat.reduceSub, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]

private theorem k197_reflect_to1165 {r : ℝ} (hr : r ∈ Set.Icc 328 1165) :
    14.21 ≤ 21 / 8 + Real.log (r ^ 2) ∧
      0.00000000998 ≤ Real.exp (-(11 / 10) * (21 / 8 + Real.log (r ^ 2))) := by
  have h₀ := (by norm_num only : (0 : ℝ) < 328).trans_le hr.1
  have hl :=
    (Analysis.rationalLogIntervalCheck_sound (N := 328) (j := 9) (n := 27) (lo := 5.793) (hi := 6)
        (by decide +kernel)).1
  have hu :=
    (Analysis.rationalLogIntervalCheck_sound (N := 1165) (j := 10) (n := 27) (lo := 5) (hi := 7.061)
        (by decide +kernel)).2
  have he :=
    (Analysis.rationalLogIntervalCheck_sound (N := 100000000000 / 998) (j := 26) (n := 32) (lo :=
        18.422) (hi := 19) (by decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div, Rat.cast_ofScientific] at hl hu he
  have hz : 14.21 ≤ 21 / 8 + Real.log (r ^ 2) := by
    rw [Real.log_pow]
    linarith only [hl, Real.log_le_log (by norm_num only : (0 : ℝ) < 328) hr.1]
  have hru : r ≤ (1165 : ℝ) := by linarith only [hr.2]
  have hd : 0.00000000998 ≤ Real.exp (-(11 / 10) * (21 / 8 + Real.log (r ^ 2))) := by
    apply (Real.log_le_iff_le_exp (by norm_num only)).mp
    have hi : Real.log (0.00000000998 : ℝ)⁻¹ ≥ 18.422 := by
      norm_num only at he ⊢; exact he
    rw [Real.log_inv] at hi
    rw [Real.log_pow]
    linarith only [hi, hu, Real.log_le_log h₀ hru]
  exact ⟨hz, hd⟩

/-- The prefix through 2701 gives a uniform lower bound for three copies
of the principal reflected Euler series through radius 1165. -/
theorem gaussian_k197_reflect_credit_to1165 {r : ℝ} (hr : r ∈ Set.Icc 328 1165) :
    0.00059 ≤ 3 * quarterMainEuler656 (1 : DirichletCharacter ℂ 1) (r ^ 2) := by
  obtain ⟨hz, hd⟩ := k197_reflect_to1165 hr
  exact reflect_credit_of_exp hr.1 hz hd (by norm_num only)

private theorem first_rectangle_to1165 {z : ℝ} (hl : 14.232 ≤ z) (hu : z ≤ 16.747) :
    0.0067 ≤ quarterGammaFirst656 z := by
  have ht :=
    (Analysis.rationalLogIntervalCheck_sound (N := 1000000 / 196) (j := 13) (n := 48) (lo := 8)
        (hi := 8.538) (by decide +kernel)).2
  have hf :=
    (Analysis.rationalLogIntervalCheck_sound (N := 1000000 / 230) (j := 12) (n := 48) (lo := 8.377)
        (hi := 9) (by decide +kernel)).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at ht hf
  have htail : Real.exp (-(3 / 5 : ℝ) * 14.232) ≤ 0.000196 := by
    rw [neg_mul]
    apply exp_neg_le_of_log_inv (by norm_num only)
    norm_num only at ht ⊢
    linarith only [ht]
  have hfront : 0.000230 ≤ Real.exp (-(1 / 2 : ℝ) * 16.747) := by
    rw [neg_mul]
    apply le_exp_neg_of_log_inv (by norm_num only)
    norm_num only at hf ⊢
    linarith only [hf]
  have hm :=
    first_moment_lower_of_exp htail (m := 2194)
      (by norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat, Nat.cast_one])
      (by norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat, Nat.cast_one])
  exact
    first_rectangle_lower (c := 0.0067) (by norm_num only) hl hu hfront hm (by norm_num only)
      (by norm_num only)

/-- The first Gamma pole gives a uniform credit for radii between 663/2
and 1165, covering the middle K197 radii. -/
theorem quarter_gamma_k197_to1165 {r : ℝ} (hr : r ∈ Set.Icc (663 / 2) 1165) :
    (centralGammaPair656 (1 : DirichletCharacter ℂ 1) (r ^ 2)).re ≤
      -2.16 * quarterWeight656 (r ^ 2) 1 - 0.0067 := by
  have hl :=
    (Analysis.rationalLogIntervalCheck_sound (N := 663 / 2) (j := 9) (n := 32) (lo := 5.8035) (hi :=
        6) (by decide +kernel)).1
  have hu :=
    (Analysis.rationalLogIntervalCheck_sound (N := 1165) (j := 10) (n := 32) (lo := 5) (hi := 7.061)
        (by decide +kernel)).2
  simp only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hl hu
  have hr₀ : 0 < r := (by norm_num only : (0 : ℝ) < 663 / 2).trans_le hr.1
  have hlo := Real.log_le_log (by norm_num only : (0 : ℝ) < 663 / 2) hr.1
  have hup := Real.log_le_log hr₀ hr.2
  have hfirst : 0.0067 ≤ quarterGammaFirst656 (Real.log (r ^ 2) + 21 / 8) := by
    rw [Real.log_pow]
    exact first_rectangle_to1165 (by linarith only [hl, hlo]) (by linarith only [hu, hup])
  exact
    (quarter_principal_gamma_upper_656 ((by norm_num only : (322 : ℝ) ≤ 663 / 2).trans hr.1)).trans
      (sub_le_sub_left hfirst _)

private theorem k197_log_credit_to1165 {r : ℝ} (hr : r ∈ Set.Icc (663 / 2) 1165) :
    0.00058 ≤ 4 * quarterWeight656 (r ^ 2) (r ^ 2) * Real.log (2 * Real.pi) := by
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
      ((by norm_num only : (0 : ℝ) ≤ 0.09319731 / 1165).trans hw)
  linarith only [h]

/-- On the middle K197 radii through 1165, any certified signed boundary
cost gives a principal-sum lower bound including the Gamma term. -/
theorem gaussian_k197_principal_to1165 (hRH : RiemannHypothesis) {r B : ℝ}
    (hr : r ∈ Set.Icc (663 / 2) 1165)
    (hb : -4 * (Chebyshev.psi (r ^ 2) - r ^ 2) * quarterWeight656 (r ^ 2) (r ^ 2) ≤ B) :
    let x := r ^ 2
    let W := fun n ↦ (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) x n).re
    (0.71780481 : ℝ) * r - 0.0065 - B <
      4 * (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, W n) - (∑' n, W n) -
        3 * (centralGammaPair656 (1 : DirichletCharacter ℂ 1) x).re := by
  intro x W
  have h :=
    gaussian_principal_gamma_lower hRH ((by norm_num only : (331 : ℝ) ≤ 663 / 2).trans hr.1)
      (quarter_gamma_k197_to1165 hr) hb (k197_log_credit_to1165 hr)
  dsimp only [x, W] at h ⊢
  linarith only [h]

/-- At radii from 995.6, bound the two K197 conductor terms
using the certified endpoint and the scale floor 1.02. -/
theorem conductors_from9956 {r s : ℝ} (hr : (9956 / 10 : ℝ) ≤ r) (hs : 1.02 ≤ s) :
    -1.422776 ≤ gaussianTheta197 r ∧
      4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 0.887022 := by
  have hl :=
    Analysis.rationalLogIntervalCheck_sound (N := 9956 / 10) (j := 10) (n := 27) (lo := 6.90325)
      (hi := 6.90336) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hl
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 9956 / 10) (p := 6)
        (d := 5) (lo := 0) (hi := 0.000252523) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat, neg_div] at hp
  norm_num only at hr
  exact
    conductors_from_endpoint (z := 13.80672) (C := 0.904761) (by norm_num only) hr hs
      (by linarith only [hl.1]) (by linarith only [hl.2]) hp
      (by norm_num only [gaussianConductorPoly197]) (by norm_num only) (by norm_num only)
      (by norm_num only)

/-- At radii from 1003.9, bound the two K197 conductor terms
using the certified endpoint and the scale floor 1.02. -/
theorem conductors_from10039 {r s : ℝ} (hr : (10039 / 10 : ℝ) ≤ r) (hs : 1.02 ≤ s) :
    -1.413862 ≤ gaussianTheta197 r ∧
      4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 0.882675 := by
  have hl :=
    Analysis.rationalLogIntervalCheck_sound (N := 10039 / 10) (j := 10) (n := 27) (lo := 6.91155)
      (hi := 6.91166) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hl
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 10039 / 10) (p := 6)
        (d := 5) (lo := 0) (hi := 0.000250020) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat, neg_div] at hp
  norm_num only at hr
  exact
    conductors_from_endpoint (z := 13.82332) (C := 0.900327) (by norm_num only) hr hs
      (by linarith only [hl.1]) (by linarith only [hl.2]) hp
      (by norm_num only [gaussianConductorPoly197]) (by norm_num only) (by norm_num only)
      (by norm_num only)

/-- At radii from 1020.5, bound the two K197 conductor terms
using the certified endpoint and the scale floor 1.02. -/
theorem conductors_from10205 {r s : ℝ} (hr : (10205 / 10 : ℝ) ≤ r) (hs : 1.02 ≤ s) :
    -1.396378 ≤ gaussianTheta197 r ∧
      4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 0.874135 := by
  have hl :=
    Analysis.rationalLogIntervalCheck_sound (N := 10205 / 10) (j := 10) (n := 27) (lo := 6.92795)
      (hi := 6.92806) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hl
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 10205 / 10) (p := 6)
        (d := 5) (lo := 0) (hi := 0.000245147) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat, neg_div] at hp
  norm_num only at hr
  exact
    conductors_from_endpoint (z := 13.85612) (C := 0.891616) (by norm_num only) hr hs
      (by linarith only [hl.1]) (by linarith only [hl.2]) hp
      (by norm_num only [gaussianConductorPoly197]) (by norm_num only) (by norm_num only)
      (by norm_num only)

/-- At radii from 1028.8, bound the two K197 conductor terms
using the certified endpoint and the scale floor 1.02. -/
theorem conductors_from10288 {r s : ℝ} (hr : (10288 / 10 : ℝ) ≤ r) (hs : 1.02 ≤ s) :
    -1.387811 ≤ gaussianTheta197 r ∧
      4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 0.869944 := by
  have hl :=
    Analysis.rationalLogIntervalCheck_sound (N := 10288 / 10) (j := 10) (n := 27) (lo := 6.93605)
      (hi := 6.93616) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hl
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 10288 / 10) (p := 6)
        (d := 5) (lo := 0) (hi := 0.000242776) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat, neg_div] at hp
  norm_num only at hr
  exact
    conductors_from_endpoint (z := 13.87232) (C := 0.887341) (by norm_num only) hr hs
      (by linarith only [hl.1]) (by linarith only [hl.2]) hp
      (by norm_num only [gaussianConductorPoly197]) (by norm_num only) (by norm_num only)
      (by norm_num only)

/-- At radii from 1036.5, bound the two K197 conductor terms
using the certified endpoint and the scale floor 1.02. -/
theorem conductors_from10365 {r s : ℝ} (hr : (10365 / 10 : ℝ) ≤ r) (hs : 1.02 ≤ s) :
    -1.379960 ≤ gaussianTheta197 r ∧
      4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 0.866099 := by
  have hl :=
    Analysis.rationalLogIntervalCheck_sound (N := 10365 / 10) (j := 10) (n := 27) (lo := 6.94350)
      (hi := 6.94362) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hl
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 10365 / 10) (p := 6)
        (d := 5) (lo := 0) (hi := 0.000240613) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat, neg_div] at hp
  norm_num only at hr
  exact
    conductors_from_endpoint (z := 13.88724) (C := 0.883419) (by norm_num only) hr hs
      (by linarith only [hl.1]) (by linarith only [hl.2]) hp
      (by norm_num only [gaussianConductorPoly197]) (by norm_num only) (by norm_num only)
      (by norm_num only)

/-- At radii from 1037.2, bound the two K197 conductor terms
using the certified endpoint and the scale floor 1.02. -/
theorem conductors_from10372 {r s : ℝ} (hr : (10372 / 10 : ℝ) ≤ r) (hs : 1.02 ≤ s) :
    -1.379253 ≤ gaussianTheta197 r ∧
      4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 0.865752 := by
  have hl :=
    Analysis.rationalLogIntervalCheck_sound (N := 10372 / 10) (j := 10) (n := 27) (lo := 6.94418)
      (hi := 6.94430) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hl
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 10372 / 10) (p := 6)
        (d := 5) (lo := 0) (hi := 0.000240418) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat, neg_div] at hp
  norm_num only at hr
  exact
    conductors_from_endpoint (z := 13.88860) (C := 0.883066) (by norm_num only) hr hs
      (by linarith only [hl.1]) (by linarith only [hl.2]) hp
      (by norm_num only [gaussianConductorPoly197]) (by norm_num only) (by norm_num only)
      (by norm_num only)

/-- At radii from 1043.8, bound the two K197 conductor terms
using the certified endpoint and the scale floor 1.02. -/
theorem conductors_from10438 {r s : ℝ} (hr : (10438 / 10 : ℝ) ≤ r) (hs : 1.02 ≤ s) :
    -1.372604 ≤ gaussianTheta197 r ∧
      4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 0.862492 := by
  have hl :=
    Analysis.rationalLogIntervalCheck_sound (N := 10438 / 10) (j := 10) (n := 27) (lo := 6.95052)
      (hi := 6.95064) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hl
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 10438 / 10) (p := 6)
        (d := 5) (lo := 0) (hi := 0.000238595) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat, neg_div] at hp
  norm_num only at hr
  exact
    conductors_from_endpoint (z := 13.90128) (C := 0.879740) (by norm_num only) hr hs
      (by linarith only [hl.1]) (by linarith only [hl.2]) hp
      (by norm_num only [gaussianConductorPoly197]) (by norm_num only) (by norm_num only)
      (by norm_num only)

/-- At radii from 1044.4, bound the two K197 conductor terms
using the certified endpoint and the scale floor 1.02. -/
theorem conductors_from10444 {r s : ℝ} (hr : (10444 / 10 : ℝ) ≤ r) (hs : 1.02 ≤ s) :
    -1.372003 ≤ gaussianTheta197 r ∧
      4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 0.862197 := by
  have hl :=
    Analysis.rationalLogIntervalCheck_sound (N := 10444 / 10) (j := 10) (n := 27) (lo := 6.95110)
      (hi := 6.95121) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hl
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 10444 / 10) (p := 6)
        (d := 5) (lo := 0) (hi := 0.000238431) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat, neg_div] at hp
  norm_num only at hr
  exact
    conductors_from_endpoint (z := 13.90242) (C := 0.879439) (by norm_num only) hr hs
      (by linarith only [hl.1]) (by linarith only [hl.2]) hp
      (by norm_num only [gaussianConductorPoly197]) (by norm_num only) (by norm_num only)
      (by norm_num only)

/-- At radii from 1044.9, bound the two K197 conductor terms
using the certified endpoint and the scale floor 1.02. -/
theorem conductors_from10449 {r s : ℝ} (hr : (10449 / 10 : ℝ) ≤ r) (hs : 1.02 ≤ s) :
    -1.371503 ≤ gaussianTheta197 r ∧
      4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 0.861951 := by
  have hl :=
    Analysis.rationalLogIntervalCheck_sound (N := 10449 / 10) (j := 10) (n := 27) (lo := 6.95158)
      (hi := 6.95169) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hl
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 10449 / 10) (p := 6)
        (d := 5) (lo := 0) (hi := 0.000238294) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat, neg_div] at hp
  norm_num only at hr
  exact
    conductors_from_endpoint (z := 13.90338) (C := 0.879189) (by norm_num only) hr hs
      (by linarith only [hl.1]) (by linarith only [hl.2]) hp
      (by norm_num only [gaussianConductorPoly197]) (by norm_num only) (by norm_num only)
      (by norm_num only)

/-- At radii from 1045.5, bound the two K197 conductor terms
using the certified endpoint and the scale floor 1.02. -/
theorem conductors_from10455 {r s : ℝ} (hr : (10455 / 10 : ℝ) ≤ r) (hs : 1.02 ≤ s) :
    -1.370907 ≤ gaussianTheta197 r ∧
      4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 0.861660 := by
  have hl :=
    Analysis.rationalLogIntervalCheck_sound (N := 10455 / 10) (j := 10) (n := 27) (lo := 6.95215)
      (hi := 6.95227) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hl
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 10455 / 10) (p := 6)
        (d := 5) (lo := 0) (hi := 0.000238130) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat, neg_div] at hp
  norm_num only at hr
  exact
    conductors_from_endpoint (z := 13.90454) (C := 0.878892) (by norm_num only) hr hs
      (by linarith only [hl.1]) (by linarith only [hl.2]) hp
      (by norm_num only [gaussianConductorPoly197]) (by norm_num only) (by norm_num only)
      (by norm_num only)

/-- At radii from 1053.8, bound the two K197 conductor terms
using the certified endpoint and the scale floor 1.02. -/
theorem conductors_from10538 {r s : ℝ} (hr : (10538 / 10 : ℝ) ≤ r) (hs : 1.02 ≤ s) :
    -1.362659 ≤ gaussianTheta197 r ∧
      4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 0.857609 := by
  have hl :=
    Analysis.rationalLogIntervalCheck_sound (N := 10538 / 10) (j := 10) (n := 27) (lo := 6.96006)
      (hi := 6.96017) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hl
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 10538 / 10) (p := 6)
        (d := 5) (lo := 0) (hi := 0.000235881) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat, neg_div] at hp
  norm_num only at hr
  exact
    conductors_from_endpoint (z := 13.92034) (C := 0.874760) (by norm_num only) hr hs
      (by linarith only [hl.1]) (by linarith only [hl.2]) hp
      (by norm_num only [gaussianConductorPoly197]) (by norm_num only) (by norm_num only)
      (by norm_num only)

/-- At radii from 1062.1, bound the two K197 conductor terms
using the certified endpoint and the scale floor 1.02. -/
theorem conductors_from10621 {r s : ℝ} (hr : (10621 / 10 : ℝ) ≤ r) (hs : 1.02 ≤ s) :
    -1.354525 ≤ gaussianTheta197 r ∧
      4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 0.853613 := by
  have hl :=
    Analysis.rationalLogIntervalCheck_sound (N := 10621 / 10) (j := 10) (n := 27) (lo := 6.96790)
      (hi := 6.96802) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hl
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 10621 / 10) (p := 6)
        (d := 5) (lo := 0) (hi := 0.000233671) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat, neg_div] at hp
  norm_num only at hr
  exact
    conductors_from_endpoint (z := 13.93604) (C := 0.870684) (by norm_num only) hr hs
      (by linarith only [hl.1]) (by linarith only [hl.2]) hp
      (by norm_num only [gaussianConductorPoly197]) (by norm_num only) (by norm_num only)
      (by norm_num only)

/-- At radii from 1070.5, bound the two K197 conductor terms
using the certified endpoint and the scale floor 1.02. -/
theorem conductors_from10705 {r s : ℝ} (hr : (10705 / 10 : ℝ) ≤ r) (hs : 1.02 ≤ s) :
    -1.346392 ≤ gaussianTheta197 r ∧
      4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 0.849611 := by
  have hl :=
    Analysis.rationalLogIntervalCheck_sound (N := 10705 / 10) (j := 10) (n := 27) (lo := 6.97578)
      (hi := 6.97590) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hl
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 10705 / 10) (p := 6)
        (d := 5) (lo := 0) (hi := 0.000231472) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat, neg_div] at hp
  norm_num only at hr
  exact
    conductors_from_endpoint (z := 13.95180) (C := 0.866602) (by norm_num only) hr hs
      (by linarith only [hl.1]) (by linarith only [hl.2]) hp
      (by norm_num only [gaussianConductorPoly197]) (by norm_num only) (by norm_num only)
      (by norm_num only)

/-- At radii from 1078.8, bound the two K197 conductor terms
using the certified endpoint and the scale floor 1.02. -/
theorem conductors_from10788 {r s : ℝ} (hr : (10788 / 10 : ℝ) ≤ r) (hs : 1.02 ≤ s) :
    -1.338458 ≤ gaussianTheta197 r ∧
      4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 0.845702 := by
  have hl :=
    Analysis.rationalLogIntervalCheck_sound (N := 10788 / 10) (j := 10) (n := 27) (lo := 6.98350)
      (hi := 6.98362) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hl
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 10788 / 10) (p := 6)
        (d := 5) (lo := 0) (hi := 0.000229337) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat, neg_div] at hp
  norm_num only at hr
  exact
    conductors_from_endpoint (z := 13.96724) (C := 0.862615) (by norm_num only) hr hs
      (by linarith only [hl.1]) (by linarith only [hl.2]) hp
      (by norm_num only [gaussianConductorPoly197]) (by norm_num only) (by norm_num only)
      (by norm_num only)

/-- At radii from 1095.4, bound the two K197 conductor terms
using the certified endpoint and the scale floor 1.02. -/
theorem conductors_from10954 {r s : ℝ} (hr : (10954 / 10 : ℝ) ≤ r) (hs : 1.02 ≤ s) :
    -1.322884 ≤ gaussianTheta197 r ∧
      4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 0.838017 := by
  have hl :=
    Analysis.rationalLogIntervalCheck_sound (N := 10954 / 10) (j := 10) (n := 27) (lo := 6.99877)
      (hi := 6.99889) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hl
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 10954 / 10) (p := 6)
        (d := 5) (lo := 0) (hi := 0.000225173) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat, neg_div] at hp
  norm_num only at hr
  exact
    conductors_from_endpoint (z := 13.99778) (C := 0.854776) (by norm_num only) hr hs
      (by linarith only [hl.1]) (by linarith only [hl.2]) hp
      (by norm_num only [gaussianConductorPoly197]) (by norm_num only) (by norm_num only)
      (by norm_num only)

/-- At radii from 1103.7, bound the two K197 conductor terms
using the certified endpoint and the scale floor 1.02. -/
theorem conductors_from11037 {r s : ℝ} (hr : (11037 / 10 : ℝ) ≤ r) (hs : 1.02 ≤ s) :
    -1.315237 ≤ gaussianTheta197 r ∧
      4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 0.834237 := by
  have hl :=
    Analysis.rationalLogIntervalCheck_sound (N := 11037 / 10) (j := 10) (n := 27) (lo := 7.00632)
      (hi := 7.00644) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hl
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 11037 / 10) (p := 6)
        (d := 5) (lo := 0) (hi := 0.000223142) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat, neg_div] at hp
  norm_num only at hr
  exact
    conductors_from_endpoint (z := 14.01288) (C := 0.850920) (by norm_num only) hr hs
      (by linarith only [hl.1]) (by linarith only [hl.2]) hp
      (by norm_num only [gaussianConductorPoly197]) (by norm_num only) (by norm_num only)
      (by norm_num only)

/-- At radii from 1112.1, bound the two K197 conductor terms
using the certified endpoint and the scale floor 1.02. -/
theorem conductors_from11121 {r s : ℝ} (hr : (11121 / 10 : ℝ) ≤ r) (hs : 1.02 ≤ s) :
    -1.307594 ≤ gaussianTheta197 r ∧
      4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 0.830454 := by
  have hl :=
    Analysis.rationalLogIntervalCheck_sound (N := 11121 / 10) (j := 10) (n := 27) (lo := 7.01391)
      (hi := 7.01402) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hl
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 11121 / 10) (p := 6)
        (d := 5) (lo := 0) (hi := 0.000221121) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat, neg_div] at hp
  norm_num only at hr
  exact
    conductors_from_endpoint (z := 14.02804) (C := 0.847062) (by norm_num only) hr hs
      (by linarith only [hl.1]) (by linarith only [hl.2]) hp
      (by norm_num only [gaussianConductorPoly197]) (by norm_num only) (by norm_num only)
      (by norm_num only)

/-- At radii from 1116.2, bound the two K197 conductor terms
using the certified endpoint and the scale floor 1.02. -/
theorem conductors_from11162 {r s : ℝ} (hr : (11162 / 10 : ℝ) ≤ r) (hs : 1.02 ≤ s) :
    -1.303900 ≤ gaussianTheta197 r ∧
      4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 0.828625 := by
  have hl :=
    Analysis.rationalLogIntervalCheck_sound (N := 11162 / 10) (j := 10) (n := 27) (lo := 7.01759)
      (hi := 7.01770) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hl
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 11162 / 10) (p := 6)
        (d := 5) (lo := 0) (hi := 0.000220147) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat, neg_div] at hp
  norm_num only at hr
  exact
    conductors_from_endpoint (z := 14.03540) (C := 0.845196) (by norm_num only) hr hs
      (by linarith only [hl.1]) (by linarith only [hl.2]) hp
      (by norm_num only [gaussianConductorPoly197]) (by norm_num only) (by norm_num only)
      (by norm_num only)

/-- At radii from 1120.4, bound the two K197 conductor terms
using the certified endpoint and the scale floor 1.02. -/
theorem conductors_from11204 {r s : ℝ} (hr : (11204 / 10 : ℝ) ≤ r) (hs : 1.02 ≤ s) :
    -1.300139 ≤ gaussianTheta197 r ∧
      4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 0.826762 := by
  have hl :=
    Analysis.rationalLogIntervalCheck_sound (N := 11204 / 10) (j := 10) (n := 27) (lo := 7.02134)
      (hi := 7.02146) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hl
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 11204 / 10) (p := 6)
        (d := 5) (lo := 0) (hi := 0.000219157) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat, neg_div] at hp
  norm_num only at hr
  exact
    conductors_from_endpoint (z := 14.04292) (C := 0.843296) (by norm_num only) hr hs
      (by linarith only [hl.1]) (by linarith only [hl.2]) hp
      (by norm_num only [gaussianConductorPoly197]) (by norm_num only) (by norm_num only)
      (by norm_num only)

/-- At radii from 1128.7, bound the two K197 conductor terms
using the certified endpoint and the scale floor 1.02. -/
theorem conductors_from11287 {r s : ℝ} (hr : (11287 / 10 : ℝ) ≤ r) (hs : 1.02 ≤ s) :
    -1.292767 ≤ gaussianTheta197 r ∧
      4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 0.823104 := by
  have hl :=
    Analysis.rationalLogIntervalCheck_sound (N := 11287 / 10) (j := 10) (n := 27) (lo := 7.02872)
      (hi := 7.02884) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hl
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 11287 / 10) (p := 6)
        (d := 5) (lo := 0) (hi := 0.000217224) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat, neg_div] at hp
  norm_num only at hr
  exact
    conductors_from_endpoint (z := 14.05768) (C := 0.839565) (by norm_num only) hr hs
      (by linarith only [hl.1]) (by linarith only [hl.2]) hp
      (by norm_num only [gaussianConductorPoly197]) (by norm_num only) (by norm_num only)
      (by norm_num only)

/-- At radii from 1137, bound the two K197 conductor terms
using the certified endpoint and the scale floor 1.02. -/
theorem conductors_from11370 {r s : ℝ} (hr : (11370 / 10 : ℝ) ≤ r) (hs : 1.02 ≤ s) :
    -1.285485 ≤ gaussianTheta197 r ∧
      4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 0.819488 := by
  have hl :=
    Analysis.rationalLogIntervalCheck_sound (N := 11370 / 10) (j := 10) (n := 27) (lo := 7.03605)
      (hi := 7.03616) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hl
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 11370 / 10) (p := 6)
        (d := 5) (lo := 0) (hi := 0.000215323) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat, neg_div] at hp
  norm_num only at hr
  exact
    conductors_from_endpoint (z := 14.07232) (C := 0.835876) (by norm_num only) hr hs
      (by linarith only [hl.1]) (by linarith only [hl.2]) hp
      (by norm_num only [gaussianConductorPoly197]) (by norm_num only) (by norm_num only)
      (by norm_num only)

/-- At radii from 1145.4, bound the two K197 conductor terms
using the certified endpoint and the scale floor 1.02. -/
theorem conductors_from11454 {r s : ℝ} (hr : (11454 / 10 : ℝ) ≤ r) (hs : 1.02 ≤ s) :
    -1.278201 ≤ gaussianTheta197 r ∧
      4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 0.815866 := by
  have hl :=
    Analysis.rationalLogIntervalCheck_sound (N := 11454 / 10) (j := 10) (n := 27) (lo := 7.04341)
      (hi := 7.04352) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hl
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 11454 / 10) (p := 6)
        (d := 5) (lo := 0) (hi := 0.000213429) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat, neg_div] at hp
  norm_num only at hr
  exact
    conductors_from_endpoint (z := 14.08704) (C := 0.832182) (by norm_num only) hr hs
      (by linarith only [hl.1]) (by linarith only [hl.2]) hp
      (by norm_num only [gaussianConductorPoly197]) (by norm_num only) (by norm_num only)
      (by norm_num only)

/-- At radii from 1149.5, bound the two K197 conductor terms
using the certified endpoint and the scale floor 1.02. -/
theorem conductors_from11495 {r s : ℝ} (hr : (11495 / 10 : ℝ) ≤ r) (hs : 1.02 ≤ s) :
    -1.274683 ≤ gaussianTheta197 r ∧
      4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 0.814118 := by
  have hl :=
    Analysis.rationalLogIntervalCheck_sound (N := 11495 / 10) (j := 10) (n := 27) (lo := 7.04698)
      (hi := 7.04710) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hl
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 11495 / 10) (p := 6)
        (d := 5) (lo := 0) (hi := 0.000212516) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat, neg_div] at hp
  norm_num only at hr
  exact
    conductors_from_endpoint (z := 14.09420) (C := 0.830399) (by norm_num only) hr hs
      (by linarith only [hl.1]) (by linarith only [hl.2]) hp
      (by norm_num only [gaussianConductorPoly197]) (by norm_num only) (by norm_num only)
      (by norm_num only)

/-- At radii from 1153.7, bound the two K197 conductor terms
using the certified endpoint and the scale floor 1.02. -/
theorem conductors_from11537 {r s : ℝ} (hr : (11537 / 10 : ℝ) ≤ r) (hs : 1.02 ≤ s) :
    -1.271093 ≤ gaussianTheta197 r ∧
      4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 0.812329 := by
  have hl :=
    Analysis.rationalLogIntervalCheck_sound (N := 11537 / 10) (j := 10) (n := 27) (lo := 7.05063)
      (hi := 7.05074) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hl
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 11537 / 10) (p := 6)
        (d := 5) (lo := 0) (hi := 0.000211588) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat, neg_div] at hp
  norm_num only at hr
  exact
    conductors_from_endpoint (z := 14.10148) (C := 0.828574) (by norm_num only) hr hs
      (by linarith only [hl.1]) (by linarith only [hl.2]) hp
      (by norm_num only [gaussianConductorPoly197]) (by norm_num only) (by norm_num only)
      (by norm_num only)

/-- At radii from 1157.8, bound the two K197 conductor terms
using the certified endpoint and the scale floor 1.02. -/
theorem conductors_from11578 {r s : ℝ} (hr : (11578 / 10 : ℝ) ≤ r) (hs : 1.02 ≤ s) :
    -1.267613 ≤ gaussianTheta197 r ∧
      4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 0.810596 := by
  have hl :=
    Analysis.rationalLogIntervalCheck_sound (N := 11578 / 10) (j := 10) (n := 27) (lo := 7.05418)
      (hi := 7.05429) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hl
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 11578 / 10) (p := 6)
        (d := 5) (lo := 0) (hi := 0.000210689) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat, neg_div] at hp
  norm_num only at hr
  exact
    conductors_from_endpoint (z := 14.10858) (C := 0.826806) (by norm_num only) hr hs
      (by linarith only [hl.1]) (by linarith only [hl.2]) hp
      (by norm_num only [gaussianConductorPoly197]) (by norm_num only) (by norm_num only)
      (by norm_num only)

/-- At radii from 1161.7, bound the two K197 conductor terms
using the certified endpoint and the scale floor 1.02. -/
theorem conductors_from11617 {r s : ℝ} (hr : (11617 / 10 : ℝ) ≤ r) (hs : 1.02 ≤ s) :
    -1.264322 ≤ gaussianTheta197 r ∧
      4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 0.808955 := by
  have hl :=
    Analysis.rationalLogIntervalCheck_sound (N := 11617 / 10) (j := 10) (n := 27) (lo := 7.05754)
      (hi := 7.05765) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hl
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 11617 / 10) (p := 6)
        (d := 5) (lo := 0) (hi := 0.000209841) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat, neg_div] at hp
  norm_num only at hr
  exact
    conductors_from_endpoint (z := 14.11530) (C := 0.825133) (by norm_num only) hr hs
      (by linarith only [hl.1]) (by linarith only [hl.2]) hp
      (by norm_num only [gaussianConductorPoly197]) (by norm_num only) (by norm_num only)
      (by norm_num only)

/-- At radii from 1162, bound the two K197 conductor terms
using the certified endpoint and the scale floor 1.02. -/
theorem conductors_from11620 {r s : ℝ} (hr : (11620 / 10 : ℝ) ≤ r) (hs : 1.02 ≤ s) :
    -1.264071 ≤ gaussianTheta197 r ∧
      4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 0.808831 := by
  have hl :=
    Analysis.rationalLogIntervalCheck_sound (N := 11620 / 10) (j := 10) (n := 27) (lo := 7.05780)
      (hi := 7.05791) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hl
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 11620 / 10) (p := 6)
        (d := 5) (lo := 0) (hi := 0.000209776) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat, neg_div] at hp
  norm_num only at hr
  exact
    conductors_from_endpoint (z := 14.11582) (C := 0.825006) (by norm_num only) hr hs
      (by linarith only [hl.1]) (by linarith only [hl.2]) hp
      (by norm_num only [gaussianConductorPoly197]) (by norm_num only) (by norm_num only)
      (by norm_num only)

/-- At radii from 1163, bound the two K197 conductor terms
using the certified endpoint and the scale floor 1.02. -/
theorem conductors_from11630 {r s : ℝ} (hr : (11630 / 10 : ℝ) ≤ r) (hs : 1.02 ≤ s) :
    -1.263232 ≤ gaussianTheta197 r ∧
      4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 0.808413 := by
  have hl :=
    Analysis.rationalLogIntervalCheck_sound (N := 11630 / 10) (j := 10) (n := 27) (lo := 7.05866)
      (hi := 7.05877) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hl
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 11630 / 10) (p := 6)
        (d := 5) (lo := 0) (hi := 0.000209560) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat, neg_div] at hp
  norm_num only at hr
  exact
    conductors_from_endpoint (z := 14.11754) (C := 0.824580) (by norm_num only) hr hs
      (by linarith only [hl.1]) (by linarith only [hl.2]) hp
      (by norm_num only [gaussianConductorPoly197]) (by norm_num only) (by norm_num only)
      (by norm_num only)

end PseudoPrime.PrimeTestBounds.MillerRabin
