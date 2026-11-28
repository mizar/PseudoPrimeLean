/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Abel788
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197PowerBounds
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Profile

/-! # The K197 Abel tail through radius 1000 -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private theorem boundary_power_to1000 {x : ℝ} (hx : 619000 ≤ x) :
    x ^ (-(8 / 5) : ℝ) ≤ 0.000000002 := by
  have h :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 619000) (p := 8) (d :=
        5) (lo := 0) (hi := 0.000000002) (by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat, neg_div] at h
  exact
    (Real.rpow_le_rpow_of_nonpos (by norm_num only : (0 : ℝ) < 619000) hx (by norm_num only)).trans
      (by
        norm_num only; exact h)

private theorem profile_boundary_abs_to1000 {v : ℝ} (hv : v ∈ Set.Icc 13 13.816) :
    |gaussianProfile197 v| ≤ 10 := by
  rw [profile_expand_197, abs_le]
  have hz : 0 ≤ v - 23 / 2 := by linarith only [hv.1]
  have hU : v - 23 / 2 ≤ 2.316 := by linarith only [hv.2]
  have hvlo : 1.5 ≤ v - 23 / 2 := by linarith only [hv.1]
  have hsqlo := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 1.5) hvlo 2
  have hsq : (v - 23 / 2) ^ 2 ≤ (v - 23 / 2) * 2.316 := by
    rw [pow_two]
    exact mul_le_mul_of_nonneg_left hU hz
  have h := profile_coeff_bounds_197
  have h₀ := mul_le_mul_of_nonneg_right h.2.1.1 hz
  have h₁ := mul_le_mul_of_nonneg_right h.2.1.2 hz
  have h₂ := mul_le_mul_of_nonneg_right h.2.2.1 (sq_nonneg (v - 23 / 2))
  have h₃ := mul_le_mul_of_nonneg_right h.2.2.2 (sq_nonneg (v - 23 / 2))
  exact ⟨by linarith only [h.1.1, h₀, h₂, hU, hsqlo], by linarith only [h.1.2, h₁, h₃, hz, hsq]⟩

/-- On the squared cutoffs from radius 787 to 1000 the finite Chebyshev envelope
and the signed profile box bound the remaining Abel boundary term. -/
theorem gaussian_abel_boundary_to1000 {x : ℝ} (hx : 619000 ≤ x) (hU : x ≤ 1000 ^ 2)
    (hl : Real.log x ∈ Set.Icc 13 13.816) :
    -(Chebyshev.psi x - x) * gaussianDensity197 x ≤ 0.000020 := by
  have hxp : 0 ≤ x := (by norm_num only : (0 : ℝ) ≤ 619000).trans hx
  have hψ :=
    AnalyticNumberTheory.Arithmetic.psi_four_fifths_1423_million
      ((by norm_num only : (1423 : ℝ) ≤ 619000).trans hx) (hU.trans (by norm_num only))
  have hs : Real.sqrt x ≤ 1000 := (Real.sqrt_le_iff).mpr ⟨by norm_num only, hU⟩
  have he : |Chebyshev.psi x - x| ≤ (800 : ℝ) := by linarith only [hψ, hs]
  have hd : |gaussianDensity197 x| ≤ (0.00000002 : ℝ) := by
    rw [gaussianDensity197, abs_mul, abs_of_nonneg (Real.rpow_nonneg hxp _)]
    have h :=
      mul_le_mul (boundary_power_to1000 hx) (profile_boundary_abs_to1000 hl) (abs_nonneg _)
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
    (hC : 0 ≤ C) (hCp : p * C ≤ 0.0065) :
    (∫ t in Set.Ioi (r ^ 2), gaussianDensity197 t) ≤ 0.0065 := by
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

private theorem main_box_787 {r : ℝ} (hr : r ∈ Set.Icc 787 817) :
    (∫ t in Set.Ioi (r ^ 2), gaussianDensity197 t) ≤ 0.0065 := by
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := (787 : ℚ) ^ 2) (p := 3)
        (d := 5) (lo := 0) (hi := 0.000334836) (by decide +kernel)).2
  norm_num only [Rat.cast_pow, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat] at hp
  have hlo :=
    (Analysis.rationalLogIntervalCheck_sound (N := 787) (j := 9) (n := 27) (lo := 6.34) (hi := 7)
        (by decide +kernel)).1
  have hup :=
    (Analysis.rationalLogIntervalCheck_sound (N := 817) (j := 9) (n := 27) (lo := 6) (hi := 6.70565)
        (by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_ofScientific] at hlo hup
  have hr₀ : 0 < r := (by norm_num only : (0 : ℝ) < 787).trans_le hr.1
  have hv : Real.log (r ^ 2) - 23 / 2 ∈ Set.Icc 0 1.91130 := by
    rw [Real.log_pow, Nat.cast_ofNat]
    exact
      ⟨by linarith only [hlo, Real.log_le_log (by norm_num only : (0 : ℝ) < 787) hr.1], by
        linarith only [hup, Real.log_le_log hr₀ hr.2]⟩
  refine
    main_integral_box (p := 0.000334836) (C := 18.345) (by norm_num only) hr.1
      (by
        norm_num only at hp ⊢; exact hp)
      hv ?_ (by norm_num only) (by norm_num only)
  intro v hw
  have hs : v ^ 2 ≤ v * 1.91130 := by
    rw [pow_two]
    exact mul_le_mul_of_nonneg_left hw.2 hw.1
  linarith only [hs, hw.2]

private theorem main_box_817 {r : ℝ} (hr : r ∈ Set.Icc 817 850) :
    (∫ t in Set.Ioi (r ^ 2), gaussianDensity197 t) ≤ 0.0065 := by
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := (817 : ℚ) ^ 2) (p := 3)
        (d := 5) (lo := 0) (hi := 0.000320137) (by decide +kernel)).2
  norm_num only [Rat.cast_pow, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat] at hp
  have hlo :=
    (Analysis.rationalLogIntervalCheck_sound (N := 817) (j := 9) (n := 27) (lo := 6.34) (hi := 7)
        (by decide +kernel)).1
  have hup :=
    (Analysis.rationalLogIntervalCheck_sound (N := 850) (j := 10) (n := 27) (lo := 6) (hi :=
        6.74525) (by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_ofScientific] at hlo hup
  have hr₀ : 0 < r := (by norm_num only : (0 : ℝ) < 817).trans_le hr.1
  have hv : Real.log (r ^ 2) - 23 / 2 ∈ Set.Icc 0 1.99050 := by
    rw [Real.log_pow, Nat.cast_ofNat]
    exact
      ⟨by linarith only [hlo, Real.log_le_log (by norm_num only : (0 : ℝ) < 817) hr.1], by
        linarith only [hup, Real.log_le_log hr₀ hr.2]⟩
  refine
    main_integral_box (p := 0.000320137) (C := 19.386) (by norm_num only) hr.1
      (by
        norm_num only at hp ⊢; exact hp)
      hv ?_ (by norm_num only) (by norm_num only)
  intro v hw
  have hs : v ^ 2 ≤ v * 1.99050 := by
    rw [pow_two]
    exact mul_le_mul_of_nonneg_left hw.2 hw.1
  linarith only [hs, hw.2]

private theorem main_box_850 {r : ℝ} (hr : r ∈ Set.Icc 850 900) :
    (∫ t in Set.Ioi (r ^ 2), gaussianDensity197 t) ≤ 0.0065 := by
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := (850 : ℚ) ^ 2) (p := 3)
        (d := 5) (lo := 0) (hi := 0.000305281) (by decide +kernel)).2
  norm_num only [Rat.cast_pow, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat] at hp
  have hlo :=
    (Analysis.rationalLogIntervalCheck_sound (N := 850) (j := 10) (n := 27) (lo := 6.34) (hi := 7)
        (by decide +kernel)).1
  have hup :=
    (Analysis.rationalLogIntervalCheck_sound (N := 900) (j := 10) (n := 27) (lo := 6) (hi :=
        6.80241) (by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_ofScientific] at hlo hup
  have hr₀ : 0 < r := (by norm_num only : (0 : ℝ) < 850).trans_le hr.1
  have hv : Real.log (r ^ 2) - 23 / 2 ∈ Set.Icc 0 2.10482 := by
    rw [Real.log_pow, Nat.cast_ofNat]
    exact
      ⟨by linarith only [hlo, Real.log_le_log (by norm_num only : (0 : ℝ) < 850) hr.1], by
        linarith only [hup, Real.log_le_log hr₀ hr.2]⟩
  refine
    main_integral_box (p := 0.000305281) (C := 20.965) (by norm_num only) hr.1
      (by
        norm_num only at hp ⊢; exact hp)
      hv ?_ (by norm_num only) (by norm_num only)
  intro v hw
  have hs : v ^ 2 ≤ v * 2.10482 := by
    rw [pow_two]
    exact mul_le_mul_of_nonneg_left hw.2 hw.1
  linarith only [hs, hw.2]

private theorem main_box_900 {r : ℝ} (hr : r ∈ Set.Icc 900 950) :
    (∫ t in Set.Ioi (r ^ 2), gaussianDensity197 t) ≤ 0.0065 := by
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := (900 : ℚ) ^ 2) (p := 3)
        (d := 5) (lo := 0) (hi := 0.000285044) (by decide +kernel)).2
  norm_num only [Rat.cast_pow, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat] at hp
  have hlo :=
    (Analysis.rationalLogIntervalCheck_sound (N := 900) (j := 10) (n := 27) (lo := 6.34) (hi := 7)
        (by decide +kernel)).1
  have hup :=
    (Analysis.rationalLogIntervalCheck_sound (N := 950) (j := 10) (n := 27) (lo := 6) (hi :=
        6.85648) (by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_ofScientific] at hlo hup
  have hr₀ : 0 < r := (by norm_num only : (0 : ℝ) < 900).trans_le hr.1
  have hv : Real.log (r ^ 2) - 23 / 2 ∈ Set.Icc 0 2.21296 := by
    rw [Real.log_pow, Nat.cast_ofNat]
    exact
      ⟨by linarith only [hlo, Real.log_le_log (by norm_num only : (0 : ℝ) < 900) hr.1], by
        linarith only [hup, Real.log_le_log hr₀ hr.2]⟩
  refine
    main_integral_box (p := 0.000285044) (C := 22.542) (by norm_num only) hr.1
      (by
        norm_num only at hp ⊢; exact hp)
      hv ?_ (by norm_num only) (by norm_num only)
  intro v hw
  have hs : v ^ 2 ≤ v * 2.21296 := by
    rw [pow_two]
    exact mul_le_mul_of_nonneg_left hw.2 hw.1
  linarith only [hs, hw.2]

private theorem main_box_950 {r : ℝ} (hr : r ∈ Set.Icc 950 1000) :
    (∫ t in Set.Ioi (r ^ 2), gaussianDensity197 t) ≤ 0.0065 := by
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := (950 : ℚ) ^ 2) (p := 3)
        (d := 5) (lo := 0) (hi := 0.000267137) (by decide +kernel)).2
  norm_num only [Rat.cast_pow, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat] at hp
  have hlo :=
    (Analysis.rationalLogIntervalCheck_sound (N := 950) (j := 10) (n := 27) (lo := 6.34) (hi := 7)
        (by decide +kernel)).1
  have hup :=
    (Analysis.rationalLogIntervalCheck_sound (N := 1000) (j := 10) (n := 27) (lo := 6) (hi :=
        6.90777) (by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_ofScientific] at hlo hup
  have hr₀ : 0 < r := (by norm_num only : (0 : ℝ) < 950).trans_le hr.1
  have hv : Real.log (r ^ 2) - 23 / 2 ∈ Set.Icc 0 2.31554 := by
    rw [Real.log_pow, Nat.cast_ofNat]
    exact
      ⟨by linarith only [hlo, Real.log_le_log (by norm_num only : (0 : ℝ) < 950) hr.1], by
        linarith only [hup, Real.log_le_log hr₀ hr.2]⟩
  refine
    main_integral_box (p := 0.000267137) (C := 24.111) (by norm_num only) hr.1
      (by
        norm_num only at hp ⊢; exact hp)
      hv ?_ (by norm_num only) (by norm_num only)
  intro v hw
  have hs : v ^ 2 ≤ v * 2.31554 := by
    rw [pow_two]
    exact mul_le_mul_of_nonneg_left hw.2 hw.1
  linarith only [hs, hw.2]

private theorem gaussian_profile_main_to1000 {r : ℝ} (hr : r ∈ Set.Icc 787 1000) :
    (∫ t in Set.Ioi (r ^ 2), gaussianDensity197 t) ≤ 0.0065 := by
  by_cases h817 : r ≤ 817
  · exact main_box_787 ⟨hr.1, h817⟩
  by_cases h850 : r ≤ 850
  · exact main_box_817 ⟨le_of_not_ge h817, h850⟩
  by_cases h900 : r ≤ 900
  · exact main_box_850 ⟨le_of_not_ge h850, h900⟩
  by_cases h950 : r ≤ 950
  · exact main_box_900 ⟨le_of_not_ge h900, h950⟩
  exact main_box_950 ⟨le_of_not_ge h950, hr.2⟩

/-- Combine the signed density integral, boundary, and Abel error into
one upper bound for substitution in the K197 comparison through radius 1000. -/
theorem gaussian_abel_tail_to1000 {r : ℝ} (hr : r ∈ Set.Icc 787 1000) :
    let x := r ^ 2
    (∫ t in Set.Ioi x, gaussianDensity197 t) - (Chebyshev.psi x - x) * gaussianDensity197 x +
        gaussianAbelError197 x ≤
      0.00683 := by
  intro x
  have hp : 0 < r := (by norm_num only : (0 : ℝ) < 787).trans_le hr.1
  have hL : (619000 : ℝ) ≤ x :=
    (by norm_num only : (619000 : ℝ) ≤ 787 ^ 2).trans (pow_le_pow_left₀ (by norm_num only) hr.1 2)
  have hU : x ≤ 1000 ^ 2 := pow_le_pow_left₀ hp.le hr.2 2
  have hlog : Real.log x ∈ Set.Icc 13 13.816 := by
    have h :=
      (Analysis.rationalLogIntervalCheck_sound (N := 1000) (j := 10) (n := 27) (lo := 5) (hi :=
          6.908) (by decide +kernel)).2
    simp only [Rat.cast_ofScientific] at h
    dsimp only [x]
    rw [Real.log_pow, Nat.cast_ofNat]
    have hL₀ :=
      (Analysis.rationalLogIntervalCheck_sound (N := 787) (j := 9) (n := 27) (lo := 6.5) (hi := 7)
          (by decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_ofScientific] at hL₀
    have hleft := hL₀.trans (Real.log_le_log (by norm_num only) hr.1)
    exact ⟨by linarith only [hleft], by linarith only [h, Real.log_le_log hp hr.2]⟩
  have hmain := gaussian_profile_main_to1000 hr
  have hb := gaussian_abel_boundary_to1000 hL hU hlog
  have he :=
    gaussian_abel_error_early_197 ((by norm_num only : (110000 : ℝ) ≤ 619000).trans hL)
      (hU.trans (by norm_num only))
  dsimp only [x] at hb he ⊢
  linarith only [hmain, hb, he]

/-- The two overlapping Abel estimates give a common tail bound at every
radius from 336.8 through 1000. -/
theorem gaussian_abel_tail_through1000 {r : ℝ} (hr : r ∈ Set.Icc 336.8 1000) :
    let x := r ^ 2
    (∫ t in Set.Ioi x, gaussianDensity197 t) - (Chebyshev.psi x - x) * gaussianDensity197 x +
        gaussianAbelError197 x ≤
      0.00683 := by
  by_cases hm : r ≤ 788
  · exact (gaussian_abel_tail_through788 ⟨hr.1, hm⟩).trans (by norm_num only)
  · exact
      gaussian_abel_tail_to1000 ⟨(by norm_num only : (787 : ℝ) ≤ 788).trans (le_of_not_ge hm), hr.2⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
