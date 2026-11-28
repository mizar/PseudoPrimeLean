/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Abel1000
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Moments
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197PowerBounds
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Profile

/-! # The K197 Abel tail through radius 1165 -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private theorem boundary_power_to1165 {x : ℝ} (hx : 990000 ≤ x) :
    x ^ (-(8 / 5) : ℝ) ≤ 0.000000002 := by
  have h :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 990000) (p := 8) (d :=
        5) (lo := 0) (hi := 0.000000002) (by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat, neg_div] at h
  exact
    (Real.rpow_le_rpow_of_nonpos (by norm_num only : (0 : ℝ) < 990000) hx (by norm_num only)).trans
      (by
        norm_num only; exact h)

private theorem profile_boundary_abs_to1165 {v : ℝ} (hv : v ∈ Set.Icc 13 14.122) :
    |gaussianProfile197 v| ≤ 10 := by
  rw [profile_expand_197, abs_le]
  have hz : 0 ≤ v - 23 / 2 := by linarith only [hv.1]
  have hU : v - 23 / 2 ≤ 2.622 := by linarith only [hv.2]
  have hvlo : 1.5 ≤ v - 23 / 2 := by linarith only [hv.1]
  have hsqlo := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 1.5) hvlo 2
  have hsq : (v - 23 / 2) ^ 2 ≤ (v - 23 / 2) * 2.622 := by
    rw [pow_two]
    exact mul_le_mul_of_nonneg_left hU hz
  have h := profile_coeff_bounds_197
  have h₀ := mul_le_mul_of_nonneg_right h.2.1.1 hz
  have h₁ := mul_le_mul_of_nonneg_right h.2.1.2 hz
  have h₂ := mul_le_mul_of_nonneg_right h.2.2.1 (sq_nonneg (v - 23 / 2))
  have h₃ := mul_le_mul_of_nonneg_right h.2.2.2 (sq_nonneg (v - 23 / 2))
  exact ⟨by linarith only [h.1.1, h₀, h₂, hU, hsqlo], by linarith only [h.1.2, h₁, h₃, hz, hsq]⟩

/-- On the squared cutoffs from radius 995 to 1165 the Chebyshev envelopes under RH
and the signed profile box bound the remaining Abel boundary term. -/
theorem gaussian_abel_boundary_to1165 (hRH : RiemannHypothesis) {x : ℝ} (hx : 990000 ≤ x)
    (hU : x ≤ 1165 ^ 2) (hl : Real.log x ∈ Set.Icc 13 14.122) :
    -(Chebyshev.psi x - x) * gaussianDensity197 x ≤ 0.0002 := by
  have hxp : 0 ≤ x := (by norm_num only : (0 : ℝ) ≤ 990000).trans hx
  have hψ : |Chebyshev.psi x - x| ≤ Real.sqrt x * 8.31 := by
    by_cases hm : x ≤ 1000000
    · exact
        (AnalyticNumberTheory.Arithmetic.psi_four_fifths_1423_million
              ((by norm_num only : (1423 : ℝ) ≤ 990000).trans hx) hm).trans
          (by
            simpa only [mul_comm (4 / 5 : ℝ)] using
              mul_le_mul_of_nonneg_left (by norm_num only : (4 / 5 : ℝ) ≤ 8.31)
                (Real.sqrt_nonneg x))
    have hh := pow_le_pow_left₀ ((by norm_num only : (0 : ℝ) ≤ 13).trans hl.1) hl.2 2
    exact
      (euler570_psi_high hRH (le_of_not_ge hm)).trans
        (mul_le_mul_of_nonneg_left (by linarith only [hh]) (Real.sqrt_nonneg x))
  have hs : Real.sqrt x ≤ 1165 := (Real.sqrt_le_iff).mpr ⟨by norm_num only, hU⟩
  have he : |Chebyshev.psi x - x| ≤ (9700 : ℝ) := by linarith only [hψ, hs]
  have hd : |gaussianDensity197 x| ≤ (0.00000002 : ℝ) := by
    rw [gaussianDensity197, abs_mul, abs_of_nonneg (Real.rpow_nonneg hxp _)]
    have h :=
      mul_le_mul (boundary_power_to1165 hx) (profile_boundary_abs_to1165 hl) (abs_nonneg _)
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
    (hC : 0 ≤ C) (hCp : p * C ≤ 0.0064) :
    (∫ t in Set.Ioi (r ^ 2), gaussianDensity197 t) ≤ 0.0064 := by
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

private theorem main_box_995 {r : ℝ} (hr : r ∈ Set.Icc 995 1030) :
    (∫ t in Set.Ioi (r ^ 2), gaussianDensity197 t) ≤ 0.0064 := by
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := (995 : ℚ) ^ 2) (p := 3)
        (d := 5) (lo := 0) (hi := 0.000252706) (by decide +kernel)).2
  norm_num only [Rat.cast_pow, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat] at hp
  have hlo :=
    (Analysis.rationalLogIntervalCheck_sound (N := 995) (j := 10) (n := 27) (lo := 6.34) (hi := 8)
        (by decide +kernel)).1
  have hup :=
    (Analysis.rationalLogIntervalCheck_sound (N := 1030) (j := 10) (n := 27) (lo := 6) (hi :=
        6.93733) (by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_ofScientific] at hlo hup
  have hr₀ : 0 < r := (by norm_num only : (0 : ℝ) < 995).trans_le hr.1
  have hv : Real.log (r ^ 2) - 23 / 2 ∈ Set.Icc 0 2.37466 := by
    rw [Real.log_pow, Nat.cast_ofNat]
    exact
      ⟨by linarith only [hlo, Real.log_le_log (by norm_num only : (0 : ℝ) < 995) hr.1], by
        linarith only [hup, Real.log_le_log hr₀ hr.2]⟩
  refine
    main_integral_box (p := 0.000252706) (C := 25.049) (by norm_num only) hr.1
      (by
        norm_num only at hp ⊢; exact hp)
      hv ?_ (by norm_num only) (by norm_num only)
  intro v hw
  have hs : v ^ 2 ≤ v * 2.37466 := by
    rw [pow_two]
    exact mul_le_mul_of_nonneg_left hw.2 hw.1
  linarith only [hs, hw.2]

private theorem main_box_1030 {r : ℝ} (hr : r ∈ Set.Icc 1030 1065) :
    (∫ t in Set.Ioi (r ^ 2), gaussianDensity197 t) ≤ 0.0064 := by
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := (1030 : ℚ) ^ 2) (p := 3)
        (d := 5) (lo := 0) (hi := 0.000242437) (by decide +kernel)).2
  norm_num only [Rat.cast_pow, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat] at hp
  have hlo :=
    (Analysis.rationalLogIntervalCheck_sound (N := 1030) (j := 10) (n := 27) (lo := 6.34) (hi := 8)
        (by decide +kernel)).1
  have hup :=
    (Analysis.rationalLogIntervalCheck_sound (N := 1065) (j := 10) (n := 27) (lo := 6) (hi :=
        6.97075) (by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_ofScientific] at hlo hup
  have hr₀ : 0 < r := (by norm_num only : (0 : ℝ) < 1030).trans_le hr.1
  have hv : Real.log (r ^ 2) - 23 / 2 ∈ Set.Icc 0 2.44150 := by
    rw [Real.log_pow, Nat.cast_ofNat]
    exact
      ⟨by linarith only [hlo, Real.log_le_log (by norm_num only : (0 : ℝ) < 1030) hr.1], by
        linarith only [hup, Real.log_le_log hr₀ hr.2]⟩
  refine
    main_integral_box (p := 0.000242437) (C := 26.137) (by norm_num only) hr.1
      (by
        norm_num only at hp ⊢; exact hp)
      hv ?_ (by norm_num only) (by norm_num only)
  intro v hw
  have hs : v ^ 2 ≤ v * 2.44150 := by
    rw [pow_two]
    exact mul_le_mul_of_nonneg_left hw.2 hw.1
  linarith only [hs, hw.2]

private theorem main_box_1065 {r : ℝ} (hr : r ∈ Set.Icc 1065 1100) :
    (∫ t in Set.Ioi (r ^ 2), gaussianDensity197 t) ≤ 0.0064 := by
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := (1065 : ℚ) ^ 2) (p := 3)
        (d := 5) (lo := 0) (hi := 0.000232907) (by decide +kernel)).2
  norm_num only [Rat.cast_pow, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat] at hp
  have hlo :=
    (Analysis.rationalLogIntervalCheck_sound (N := 1065) (j := 10) (n := 27) (lo := 6.34) (hi := 8)
        (by decide +kernel)).1
  have hup :=
    (Analysis.rationalLogIntervalCheck_sound (N := 1100) (j := 10) (n := 27) (lo := 6) (hi :=
        7.00308) (by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_ofScientific] at hlo hup
  have hr₀ : 0 < r := (by norm_num only : (0 : ℝ) < 1065).trans_le hr.1
  have hv : Real.log (r ^ 2) - 23 / 2 ∈ Set.Icc 0 2.50616 := by
    rw [Real.log_pow, Nat.cast_ofNat]
    exact
      ⟨by linarith only [hlo, Real.log_le_log (by norm_num only : (0 : ℝ) < 1065) hr.1], by
        linarith only [hup, Real.log_le_log hr₀ hr.2]⟩
  refine
    main_integral_box (p := 0.000232907) (C := 27.220) (by norm_num only) hr.1
      (by
        norm_num only at hp ⊢; exact hp)
      hv ?_ (by norm_num only) (by norm_num only)
  intro v hw
  have hs : v ^ 2 ≤ v * 2.50616 := by
    rw [pow_two]
    exact mul_le_mul_of_nonneg_left hw.2 hw.1
  linarith only [hs, hw.2]

private theorem main_box_1100 {r : ℝ} (hr : r ∈ Set.Icc 1100 1135) :
    (∫ t in Set.Ioi (r ^ 2), gaussianDensity197 t) ≤ 0.0064 := by
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := (1100 : ℚ) ^ 2) (p := 3)
        (d := 5) (lo := 0) (hi := 0.000224043) (by decide +kernel)).2
  norm_num only [Rat.cast_pow, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat] at hp
  have hlo :=
    (Analysis.rationalLogIntervalCheck_sound (N := 1100) (j := 10) (n := 27) (lo := 6.34) (hi := 8)
        (by decide +kernel)).1
  have hup :=
    (Analysis.rationalLogIntervalCheck_sound (N := 1135) (j := 10) (n := 27) (lo := 6) (hi :=
        7.03440) (by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_ofScientific] at hlo hup
  have hr₀ : 0 < r := (by norm_num only : (0 : ℝ) < 1100).trans_le hr.1
  have hv : Real.log (r ^ 2) - 23 / 2 ∈ Set.Icc 0 2.56880 := by
    rw [Real.log_pow, Nat.cast_ofNat]
    exact
      ⟨by linarith only [hlo, Real.log_le_log (by norm_num only : (0 : ℝ) < 1100) hr.1], by
        linarith only [hup, Real.log_le_log hr₀ hr.2]⟩
  refine
    main_integral_box (p := 0.000224043) (C := 28.296) (by norm_num only) hr.1
      (by
        norm_num only at hp ⊢; exact hp)
      hv ?_ (by norm_num only) (by norm_num only)
  intro v hw
  have hs : v ^ 2 ≤ v * 2.56880 := by
    rw [pow_two]
    exact mul_le_mul_of_nonneg_left hw.2 hw.1
  linarith only [hs, hw.2]

private theorem main_box_1135 {r : ℝ} (hr : r ∈ Set.Icc 1135 1165) :
    (∫ t in Set.Ioi (r ^ 2), gaussianDensity197 t) ≤ 0.0064 := by
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := (1135 : ℚ) ^ 2) (p := 3)
        (d := 5) (lo := 0) (hi := 0.000215778) (by decide +kernel)).2
  norm_num only [Rat.cast_pow, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat] at hp
  have hlo :=
    (Analysis.rationalLogIntervalCheck_sound (N := 1135) (j := 10) (n := 27) (lo := 6.34) (hi := 8)
        (by decide +kernel)).1
  have hup :=
    (Analysis.rationalLogIntervalCheck_sound (N := 1165) (j := 10) (n := 27) (lo := 6) (hi :=
        7.06049) (by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_ofScientific] at hlo hup
  have hr₀ : 0 < r := (by norm_num only : (0 : ℝ) < 1135).trans_le hr.1
  have hv : Real.log (r ^ 2) - 23 / 2 ∈ Set.Icc 0 2.62098 := by
    rw [Real.log_pow, Nat.cast_ofNat]
    exact
      ⟨by linarith only [hlo, Real.log_le_log (by norm_num only : (0 : ℝ) < 1135) hr.1], by
        linarith only [hup, Real.log_le_log hr₀ hr.2]⟩
  refine
    main_integral_box (p := 0.000215778) (C := 29.213) (by norm_num only) hr.1
      (by
        norm_num only at hp ⊢; exact hp)
      hv ?_ (by norm_num only) (by norm_num only)
  intro v hw
  have hs : v ^ 2 ≤ v * 2.62098 := by
    rw [pow_two]
    exact mul_le_mul_of_nonneg_left hw.2 hw.1
  linarith only [hs, hw.2]

private theorem gaussian_profile_main_to1165 {r : ℝ} (hr : r ∈ Set.Icc 995 1165) :
    (∫ t in Set.Ioi (r ^ 2), gaussianDensity197 t) ≤ 0.0064 := by
  by_cases h1030 : r ≤ 1030
  · exact main_box_995 ⟨hr.1, h1030⟩
  by_cases h1065 : r ≤ 1065
  · exact main_box_1030 ⟨le_of_not_ge h1030, h1065⟩
  by_cases h1100 : r ≤ 1100
  · exact main_box_1065 ⟨le_of_not_ge h1065, h1100⟩
  by_cases h1135 : r ≤ 1135
  · exact main_box_1100 ⟨le_of_not_ge h1100, h1135⟩
  exact main_box_1135 ⟨le_of_not_ge h1135, hr.2⟩

/-- Combine the signed density integral, boundary, and Abel error into
one upper bound for substitution in the K197 comparison through radius 1165. -/
theorem gaussian_abel_tail_to1165 (hRH : RiemannHypothesis) {r : ℝ} (hr : r ∈ Set.Icc 995 1165) :
    let x := r ^ 2
    (∫ t in Set.Ioi x, gaussianDensity197 t) - (Chebyshev.psi x - x) * gaussianDensity197 x +
        gaussianAbelError197 x ≤
      0.0069 := by
  intro x
  have hp : 0 < r := (by norm_num only : (0 : ℝ) < 995).trans_le hr.1
  have hL : (990000 : ℝ) ≤ x :=
    (by norm_num only : (990000 : ℝ) ≤ 995 ^ 2).trans (pow_le_pow_left₀ (by norm_num only) hr.1 2)
  have hU : x ≤ 1165 ^ 2 := pow_le_pow_left₀ hp.le hr.2 2
  have hlog : Real.log x ∈ Set.Icc 13 14.122 := by
    have h :=
      (Analysis.rationalLogIntervalCheck_sound (N := 1165) (j := 10) (n := 27) (lo := 5) (hi :=
          7.061) (by decide +kernel)).2
    simp only [Rat.cast_ofScientific] at h
    dsimp only [x]
    rw [Real.log_pow, Nat.cast_ofNat]
    have hL₀ :=
      (Analysis.rationalLogIntervalCheck_sound (N := 995) (j := 10) (n := 27) (lo := 6.5) (hi := 7)
          (by decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_ofScientific] at hL₀
    have hleft := hL₀.trans (Real.log_le_log (by norm_num only) hr.1)
    exact ⟨by linarith only [hleft], by linarith only [h, Real.log_le_log hp hr.2]⟩
  have hmain := gaussian_profile_main_to1165 hr
  have hb := gaussian_abel_boundary_to1165 hRH hL hU hlog
  have he := gaussian_abel_error_uniform_197 ((by norm_num only : (110000 : ℝ) ≤ 990000).trans hL)
  dsimp only [x] at hb he ⊢
  linarith only [hmain, hb, he]

end PseudoPrime.PrimeTestBounds.MillerRabin
