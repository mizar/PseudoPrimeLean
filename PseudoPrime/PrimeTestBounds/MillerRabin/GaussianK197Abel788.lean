/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Abel672
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197PowerBounds
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Profile

/-! # The K197 Abel tail through radius 788 -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private theorem boundary_power_to788 {x : ℝ} (hx : 450000 ≤ x) :
    x ^ (-(8 / 5) : ℝ) ≤ 0.000000002 := by
  have h :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 450000) (p := 8) (d :=
        5) (lo := 0) (hi := 0.000000002) (by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat, neg_div] at h
  exact
    (Real.rpow_le_rpow_of_nonpos (by norm_num only : (0 : ℝ) < 450000) hx (by norm_num only)).trans
      (by
        norm_num only; exact h)

private theorem profile_boundary_abs_to788 {v : ℝ} (hv : v ∈ Set.Icc 13 13.34) :
    |gaussianProfile197 v| ≤ 5 := by
  rw [profile_expand_197, abs_le]
  have hz : 0 ≤ v - 23 / 2 := by linarith only [hv.1]
  have hU : v - 23 / 2 ≤ 1.84 := by linarith only [hv.2]
  have hvlo : 1.5 ≤ v - 23 / 2 := by linarith only [hv.1]
  have hsqlo := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 1.5) hvlo 2
  have hsq : (v - 23 / 2) ^ 2 ≤ (v - 23 / 2) * 1.84 := by
    rw [pow_two]
    exact mul_le_mul_of_nonneg_left hU hz
  have h := profile_coeff_bounds_197
  have h₀ := mul_le_mul_of_nonneg_right h.2.1.1 hz
  have h₁ := mul_le_mul_of_nonneg_right h.2.1.2 hz
  have h₂ := mul_le_mul_of_nonneg_right h.2.2.1 (sq_nonneg (v - 23 / 2))
  have h₃ := mul_le_mul_of_nonneg_right h.2.2.2 (sq_nonneg (v - 23 / 2))
  exact ⟨by linarith only [h.1.1, h₀, h₂, hU, hsqlo], by linarith only [h.1.2, h₁, h₃, hz, hsq]⟩

/-- On the squared cutoffs from radius 671 to 788 the finite Chebyshev envelope
and the signed profile box bound the remaining Abel boundary term. -/
theorem gaussian_abel_boundary_to788 {x : ℝ} (hx : 450000 ≤ x) (hU : x ≤ 788 ^ 2)
    (hl : Real.log x ∈ Set.Icc 13 13.34) :
    -(Chebyshev.psi x - x) * gaussianDensity197 x ≤ 0.000013 := by
  have hxp : 0 ≤ x := (by norm_num only : (0 : ℝ) ≤ 450000).trans hx
  have hψ :=
    AnalyticNumberTheory.Arithmetic.psi_four_fifths_1423_million
      ((by norm_num only : (1423 : ℝ) ≤ 450000).trans hx) (hU.trans (by norm_num only))
  have hs : Real.sqrt x ≤ 788 := (Real.sqrt_le_iff).mpr ⟨by norm_num only, hU⟩
  have he : |Chebyshev.psi x - x| ≤ (630.4 : ℝ) := by linarith only [hψ, hs]
  have hd : |gaussianDensity197 x| ≤ (0.00000001 : ℝ) := by
    rw [gaussianDensity197, abs_mul, abs_of_nonneg (Real.rpow_nonneg hxp _)]
    have h :=
      mul_le_mul (boundary_power_to788 hx) (profile_boundary_abs_to788 hl) (abs_nonneg _)
        (by norm_num only)
    linarith only [h]
  have h := mul_le_mul he hd (abs_nonneg _) (by norm_num only)
  have hh := le_abs_self (-(Chebyshev.psi x - x) * gaussianDensity197 x)
  rw [abs_mul, abs_neg] at hh
  linarith only [h, hh]

private theorem main_integral_box {r a p V C : ℝ} (ha : 1 ≤ a) (hr : a ≤ r)
    (hp : (a ^ 2) ^ (-(3 / 5) : ℝ) ≤ p) (hv : Real.log (r ^ 2) - 23 / 2 ∈ Set.Icc 0 V)
    (hpoly :
      ∀ v ∈ Set.Icc (0 : ℝ) V,
        (4.028663 - 7.025619 * (v + 5 / 3) + 2.061371 * (v ^ 2 + (10 / 3) * v + 50 / 9)) / (3 / 5) ≤
          C)
    (hC : 0 ≤ C) (hCp : p * C ≤ 0.006) :
    (∫ t in Set.Ioi (r ^ 2), gaussianDensity197 t) ≤ 0.006 := by
  have hb : 0 < a := zero_lt_one.trans_le ha
  have hx := pow_le_pow_left₀ hb.le hr 2
  have hp' :=
    (Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos hb) hx
          (by norm_num only : (-(3 / 5) : ℝ) ≤ 0)).trans
      hp
  refine
    (gaussian_profile_main_upper_197 (one_le_pow₀ (ha.trans hr)) (by linarith only [hv.1])).trans ?_
  exact
    (mul_le_mul_of_nonneg_left (hpoly _ hv) (Real.rpow_nonneg (sq_nonneg r) _)).trans
      ((mul_le_mul_of_nonneg_right hp' hC).trans hCp)

private theorem main_box_671 {r : ℝ} (hr : r ∈ Set.Icc 671 699) :
    (∫ t in Set.Ioi (r ^ 2), gaussianDensity197 t) ≤ 0.006 := by
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := (671 : ℚ) ^ 2) (p := 3)
        (d := 5) (lo := 0) (hi := 0.000405448) (by decide +kernel)).2
  norm_num only [Rat.cast_pow, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat] at hp
  have hlo :=
    (Analysis.rationalLogIntervalCheck_sound (N := 671) (j := 9) (n := 27) (lo := 6.34) (hi := 7)
        (by decide +kernel)).1
  have hup :=
    (Analysis.rationalLogIntervalCheck_sound (N := 699) (j := 9) (n := 27) (lo := 6) (hi := 6.54966)
        (by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_ofScientific] at hlo hup
  have hr₀ : 0 < r := (by norm_num only : (0 : ℝ) < 671).trans_le hr.1
  have hv : Real.log (r ^ 2) - 23 / 2 ∈ Set.Icc 0 1.59932 := by
    rw [Real.log_pow, Nat.cast_ofNat]
    exact
      ⟨by linarith only [hlo, Real.log_le_log (by norm_num only : (0 : ℝ) < 671) hr.1], by
        linarith only [hup, Real.log_le_log hr₀ hr.2]⟩
  refine
    main_integral_box (p := 0.000405448) (C := 14.663) (by norm_num only) hr.1
      (by
        norm_num only at hp ⊢; exact hp)
      hv ?_ (by norm_num only) (by norm_num only)
  intro v hw
  have hs : v ^ 2 ≤ v * 1.59932 := by
    rw [pow_two]
    exact mul_le_mul_of_nonneg_left hw.2 hw.1
  linarith only [hs, hw.2]

private theorem main_box_699 {r : ℝ} (hr : r ∈ Set.Icc 699 724) :
    (∫ t in Set.Ioi (r ^ 2), gaussianDensity197 t) ≤ 0.006 := by
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := (699 : ℚ) ^ 2) (p := 3)
        (d := 5) (lo := 0) (hi := 0.000386038) (by decide +kernel)).2
  norm_num only [Rat.cast_pow, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat] at hp
  have hlo :=
    (Analysis.rationalLogIntervalCheck_sound (N := 699) (j := 9) (n := 27) (lo := 6.34) (hi := 7)
        (by decide +kernel)).1
  have hup :=
    (Analysis.rationalLogIntervalCheck_sound (N := 724) (j := 9) (n := 27) (lo := 6) (hi := 6.58480)
        (by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_ofScientific] at hlo hup
  have hr₀ : 0 < r := (by norm_num only : (0 : ℝ) < 699).trans_le hr.1
  have hv : Real.log (r ^ 2) - 23 / 2 ∈ Set.Icc 0 1.66960 := by
    rw [Real.log_pow, Nat.cast_ofNat]
    exact
      ⟨by linarith only [hlo, Real.log_le_log (by norm_num only : (0 : ℝ) < 699) hr.1], by
        linarith only [hup, Real.log_le_log hr₀ hr.2]⟩
  refine
    main_integral_box (p := 0.000386038) (C := 15.434) (by norm_num only) hr.1
      (by
        norm_num only at hp ⊢; exact hp)
      hv ?_ (by norm_num only) (by norm_num only)
  intro v hw
  have hs : v ^ 2 ≤ v * 1.66960 := by
    rw [pow_two]
    exact mul_le_mul_of_nonneg_left hw.2 hw.1
  linarith only [hs, hw.2]

private theorem main_box_724 {r : ℝ} (hr : r ∈ Set.Icc 724 746) :
    (∫ t in Set.Ioi (r ^ 2), gaussianDensity197 t) ≤ 0.006 := by
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := (724 : ℚ) ^ 2) (p := 3)
        (d := 5) (lo := 0) (hi := 0.000370098) (by decide +kernel)).2
  norm_num only [Rat.cast_pow, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat] at hp
  have hlo :=
    (Analysis.rationalLogIntervalCheck_sound (N := 724) (j := 9) (n := 27) (lo := 6.34) (hi := 7)
        (by decide +kernel)).1
  have hup :=
    (Analysis.rationalLogIntervalCheck_sound (N := 746) (j := 9) (n := 27) (lo := 6) (hi := 6.61473)
        (by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_ofScientific] at hlo hup
  have hr₀ : 0 < r := (by norm_num only : (0 : ℝ) < 724).trans_le hr.1
  have hv : Real.log (r ^ 2) - 23 / 2 ∈ Set.Icc 0 1.72946 := by
    rw [Real.log_pow, Nat.cast_ofNat]
    exact
      ⟨by linarith only [hlo, Real.log_le_log (by norm_num only : (0 : ℝ) < 724) hr.1], by
        linarith only [hup, Real.log_le_log hr₀ hr.2]⟩
  refine
    main_integral_box (p := 0.000370098) (C := 16.118) (by norm_num only) hr.1
      (by
        norm_num only at hp ⊢; exact hp)
      hv ?_ (by norm_num only) (by norm_num only)
  intro v hw
  have hs : v ^ 2 ≤ v * 1.72946 := by
    rw [pow_two]
    exact mul_le_mul_of_nonneg_left hw.2 hw.1
  linarith only [hs, hw.2]

private theorem main_box_746 {r : ℝ} (hr : r ∈ Set.Icc 746 766) :
    (∫ t in Set.Ioi (r ^ 2), gaussianDensity197 t) ≤ 0.006 := by
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := (746 : ℚ) ^ 2) (p := 3)
        (d := 5) (lo := 0) (hi := 0.000357040) (by decide +kernel)).2
  norm_num only [Rat.cast_pow, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat] at hp
  have hlo :=
    (Analysis.rationalLogIntervalCheck_sound (N := 746) (j := 9) (n := 27) (lo := 6.34) (hi := 7)
        (by decide +kernel)).1
  have hup :=
    (Analysis.rationalLogIntervalCheck_sound (N := 766) (j := 9) (n := 27) (lo := 6) (hi := 6.64119)
        (by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_ofScientific] at hlo hup
  have hr₀ : 0 < r := (by norm_num only : (0 : ℝ) < 746).trans_le hr.1
  have hv : Real.log (r ^ 2) - 23 / 2 ∈ Set.Icc 0 1.78238 := by
    rw [Real.log_pow, Nat.cast_ofNat]
    exact
      ⟨by linarith only [hlo, Real.log_le_log (by norm_num only : (0 : ℝ) < 746) hr.1], by
        linarith only [hup, Real.log_le_log hr₀ hr.2]⟩
  refine
    main_integral_box (p := 0.000357040) (C := 16.743) (by norm_num only) hr.1
      (by
        norm_num only at hp ⊢; exact hp)
      hv ?_ (by norm_num only) (by norm_num only)
  intro v hw
  have hs : v ^ 2 ≤ v * 1.78238 := by
    rw [pow_two]
    exact mul_le_mul_of_nonneg_left hw.2 hw.1
  linarith only [hs, hw.2]

private theorem main_box_766 {r : ℝ} (hr : r ∈ Set.Icc 766 785) :
    (∫ t in Set.Ioi (r ^ 2), gaussianDensity197 t) ≤ 0.006 := by
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := (766 : ℚ) ^ 2) (p := 3)
        (d := 5) (lo := 0) (hi := 0.000345883) (by decide +kernel)).2
  norm_num only [Rat.cast_pow, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat] at hp
  have hlo :=
    (Analysis.rationalLogIntervalCheck_sound (N := 766) (j := 9) (n := 27) (lo := 6.34) (hi := 7)
        (by decide +kernel)).1
  have hup :=
    (Analysis.rationalLogIntervalCheck_sound (N := 785) (j := 9) (n := 27) (lo := 6) (hi := 6.66569)
        (by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_ofScientific] at hlo hup
  have hr₀ : 0 < r := (by norm_num only : (0 : ℝ) < 766).trans_le hr.1
  have hv : Real.log (r ^ 2) - 23 / 2 ∈ Set.Icc 0 1.83138 := by
    rw [Real.log_pow, Nat.cast_ofNat]
    exact
      ⟨by linarith only [hlo, Real.log_le_log (by norm_num only : (0 : ℝ) < 766) hr.1], by
        linarith only [hup, Real.log_le_log hr₀ hr.2]⟩
  refine
    main_integral_box (p := 0.000345883) (C := 17.338) (by norm_num only) hr.1
      (by
        norm_num only at hp ⊢; exact hp)
      hv ?_ (by norm_num only) (by norm_num only)
  intro v hw
  have hs : v ^ 2 ≤ v * 1.83138 := by
    rw [pow_two]
    exact mul_le_mul_of_nonneg_left hw.2 hw.1
  linarith only [hs, hw.2]

private theorem main_box_785 {r : ℝ} (hr : r ∈ Set.Icc 785 788) :
    (∫ t in Set.Ioi (r ^ 2), gaussianDensity197 t) ≤ 0.006 := by
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := (785 : ℚ) ^ 2) (p := 3)
        (d := 5) (lo := 0) (hi := 0.000335861) (by decide +kernel)).2
  norm_num only [Rat.cast_pow, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat] at hp
  have hlo :=
    (Analysis.rationalLogIntervalCheck_sound (N := 785) (j := 9) (n := 27) (lo := 6.34) (hi := 7)
        (by decide +kernel)).1
  have hup :=
    (Analysis.rationalLogIntervalCheck_sound (N := 788) (j := 9) (n := 27) (lo := 6) (hi := 6.66950)
        (by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_ofScientific] at hlo hup
  have hr₀ : 0 < r := (by norm_num only : (0 : ℝ) < 785).trans_le hr.1
  have hv : Real.log (r ^ 2) - 23 / 2 ∈ Set.Icc 0 1.83900 := by
    rw [Real.log_pow, Nat.cast_ofNat]
    exact
      ⟨by linarith only [hlo, Real.log_le_log (by norm_num only : (0 : ℝ) < 785) hr.1], by
        linarith only [hup, Real.log_le_log hr₀ hr.2]⟩
  refine
    main_integral_box (p := 0.000335861) (C := 17.432) (by norm_num only) hr.1
      (by
        norm_num only at hp ⊢; exact hp)
      hv ?_ (by norm_num only) (by norm_num only)
  intro v hw
  have hs : v ^ 2 ≤ v * 1.83900 := by
    rw [pow_two]
    exact mul_le_mul_of_nonneg_left hw.2 hw.1
  linarith only [hs, hw.2]

private theorem gaussian_profile_main_to788 {r : ℝ} (hr : r ∈ Set.Icc 671 788) :
    (∫ t in Set.Ioi (r ^ 2), gaussianDensity197 t) ≤ 0.006 := by
  by_cases h699 : r ≤ 699
  · exact main_box_671 ⟨hr.1, h699⟩
  by_cases h724 : r ≤ 724
  · exact main_box_699 ⟨le_of_not_ge h699, h724⟩
  by_cases h746 : r ≤ 746
  · exact main_box_724 ⟨le_of_not_ge h724, h746⟩
  by_cases h766 : r ≤ 766
  · exact main_box_746 ⟨le_of_not_ge h746, h766⟩
  by_cases h785 : r ≤ 785
  · exact main_box_766 ⟨le_of_not_ge h766, h785⟩
  exact main_box_785 ⟨le_of_not_ge h785, hr.2⟩

/-- Combine the signed density integral, boundary, and Abel error into
one upper bound for substitution in the K197 comparison through radius 788. -/
theorem gaussian_abel_tail_to788 {r : ℝ} (hr : r ∈ Set.Icc 671 788) :
    let x := r ^ 2
    (∫ t in Set.Ioi x, gaussianDensity197 t) - (Chebyshev.psi x - x) * gaussianDensity197 x +
        gaussianAbelError197 x ≤
      0.006305 := by
  intro x
  have hp : 0 < r := (by norm_num only : (0 : ℝ) < 671).trans_le hr.1
  have hL : (450000 : ℝ) ≤ x :=
    (by norm_num only : (450000 : ℝ) ≤ 671 ^ 2).trans (pow_le_pow_left₀ (by norm_num only) hr.1 2)
  have hU : x ≤ 788 ^ 2 := pow_le_pow_left₀ hp.le hr.2 2
  have hlog : Real.log x ∈ Set.Icc 13 13.34 := by
    have h :=
      (Analysis.rationalLogIntervalCheck_sound (N := 788) (j := 9) (n := 27) (lo := 5) (hi := 6.67)
          (by decide +kernel)).2
    simp only [Rat.cast_ofScientific] at h
    dsimp only [x]
    rw [Real.log_pow, Nat.cast_ofNat]
    have hL₀ :=
      (Analysis.rationalLogIntervalCheck_sound (N := 671) (j := 9) (n := 27) (lo := 6.5) (hi := 7)
          (by decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_ofScientific] at hL₀
    have hleft := hL₀.trans (Real.log_le_log (by norm_num only) hr.1)
    exact ⟨by linarith only [hleft], by linarith only [h, Real.log_le_log hp hr.2]⟩
  have hmain := gaussian_profile_main_to788 hr
  have hb := gaussian_abel_boundary_to788 hL hU hlog
  have he :=
    gaussian_abel_error_early_197 ((by norm_num only : (110000 : ℝ) ≤ 450000).trans hL)
      (hU.trans (by norm_num only))
  dsimp only [x] at hb he ⊢
  linarith only [hmain, hb, he]

/-- The two overlapping Abel estimates give the same tail bound at every
radius from 336.8 through 788. -/
theorem gaussian_abel_tail_through788 {r : ℝ} (hr : r ∈ Set.Icc 336.8 788) :
    let x := r ^ 2
    (∫ t in Set.Ioi x, gaussianDensity197 t) - (Chebyshev.psi x - x) * gaussianDensity197 x +
        gaussianAbelError197 x ≤
      0.006305 := by
  by_cases hm : r ≤ 672
  · exact gaussian_abel_tail_through672 ⟨hr.1, hm⟩
  · exact
      gaussian_abel_tail_to788 ⟨(by norm_num only : (671 : ℝ) ≤ 672).trans (le_of_not_ge hm), hr.2⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
