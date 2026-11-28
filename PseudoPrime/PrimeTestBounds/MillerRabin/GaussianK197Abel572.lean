/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Abel522
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197PowerBounds
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Profile

/-! # The K197 Abel tail through radius 572 -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private theorem boundary_power_to572 {x : ℝ} (hx : 270000 ≤ x) :
    x ^ (-(8 / 5) : ℝ) ≤ 0.000000004 := by
  have h :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 270000) (p := 8) (d :=
        5) (lo := 0) (hi := 0.000000004) (by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat, neg_div] at h
  exact
    (Real.rpow_le_rpow_of_nonpos (by norm_num only : (0 : ℝ) < 270000) hx (by norm_num only)).trans
      (by
        norm_num only; exact h)

private theorem main_power_to572 {r : ℝ} (hr : 521.25 ≤ r) :
    (r ^ 2) ^ (-(3 / 5) : ℝ) ≤ 0.000549 := by
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := (521.25 : ℚ) ^ 2) (p :=
        3) (d := 5) (lo := 0) (hi := 0.000549) (by decide +kernel)).2
  simp only [Rat.cast_pow, Rat.cast_ofScientific, Nat.cast_ofNat] at hp
  have hb : (521.25 : ℝ) ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (by norm_num only) hr 2
  exact
    (Real.rpow_le_rpow_of_nonpos (by norm_num only : (0 : ℝ) < 521.25 ^ 2) hb
          (by norm_num only)).trans
      (by
        norm_num only at hp ⊢; exact hp)

private theorem profile_boundary_abs_to572 {v : ℝ} (hv : v ∈ Set.Icc 11.5 12.7) :
    |gaussianProfile197 v| ≤ 5 := by
  rw [profile_expand_197, abs_le]
  have hz : 0 ≤ v - 23 / 2 := by linarith only [hv.1]
  have hU : v - 23 / 2 ≤ 1.2 := by linarith only [hv.2]
  have hsq : (v - 23 / 2) ^ 2 ≤ (v - 23 / 2) * 1.2 := by
    rw [pow_two]
    exact mul_le_mul_of_nonneg_left hU hz
  have h := profile_coeff_bounds_197
  have h₀ := mul_le_mul_of_nonneg_right h.2.1.1 hz
  have h₁ := mul_le_mul_of_nonneg_right h.2.1.2 hz
  have h₂ := mul_le_mul_of_nonneg_right h.2.2.1 (sq_nonneg (v - 23 / 2))
  have h₃ := mul_le_mul_of_nonneg_right h.2.2.2 (sq_nonneg (v - 23 / 2))
  exact
    ⟨by linarith only [h.1.1, h₀, h₂, hz, hU, sq_nonneg (v - 23 / 2)], by
      linarith only [h.1.2, h₁, h₃, hz, hsq]⟩

/-- On the squared cutoffs from radius 521.25 to 572 the finite Chebyshev envelope
and the signed profile box bound the remaining Abel boundary term. -/
theorem gaussian_abel_boundary_to572 {x : ℝ} (hx : 270000 ≤ x) (hU : x ≤ 572 ^ 2)
    (hl : Real.log x ∈ Set.Icc 11.5 12.7) :
    -(Chebyshev.psi x - x) * gaussianDensity197 x ≤ 0.000013 := by
  have hxp : 0 ≤ x := (by norm_num only : (0 : ℝ) ≤ 270000).trans hx
  have hψ :=
    AnalyticNumberTheory.Arithmetic.psi_four_fifths_1423_million
      ((by norm_num only : (1423 : ℝ) ≤ 270000).trans hx) (hU.trans (by norm_num only))
  have hs : Real.sqrt x ≤ 572 := (Real.sqrt_le_iff).mpr ⟨by norm_num only, hU⟩
  have he : |Chebyshev.psi x - x| ≤ (457.6 : ℝ) := by linarith only [hψ, hs]
  have hd : |gaussianDensity197 x| ≤ (0.00000002 : ℝ) := by
    rw [gaussianDensity197, abs_mul, abs_of_nonneg (Real.rpow_nonneg hxp _)]
    have h :=
      mul_le_mul (boundary_power_to572 hx) (profile_boundary_abs_to572 hl) (abs_nonneg _)
        (by norm_num only)
    linarith only [h]
  have h := mul_le_mul he hd (abs_nonneg _) (by norm_num only)
  have hh := le_abs_self (-(Chebyshev.psi x - x) * gaussianDensity197 x)
  rw [abs_mul, abs_neg] at hh
  linarith only [h, hh]

/-- The signed main integral costs at most 0.006 on the K197 radii from 521.25 to 572.
This bounds the combined quadratic before multiplying by the positive power. -/
theorem gaussian_profile_main_to572 {r : ℝ} (hr : r ∈ Set.Icc 521.25 572) :
    (∫ t in Set.Ioi (r ^ 2), gaussianDensity197 t) ≤ 0.006 := by
  have hr₀ : 0 < r := (by norm_num only : (0 : ℝ) < 521.25).trans_le hr.1
  have hx : 1 ≤ r ^ 2 := one_le_pow₀ ((by norm_num only : (1 : ℝ) ≤ 521.25).trans hr.1)
  have hlog0 :=
    (Analysis.rationalLogIntervalCheck_sound (N := 2085 / 4) (j := 9) (n := 27) (lo := 6.25) (hi :=
        7) (by decide +kernel)).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hlog0
  have hr' : (2085 / 4 : ℝ) ≤ r := by linarith only [hr.1]
  have hlog := hlog0.trans (Real.log_le_log (by norm_num only) hr')
  have hu :=
    (Analysis.rationalLogIntervalCheck_sound (N := 572) (j := 9) (n := 27) (lo := 5) (hi := 6.35)
        (by decide +kernel)).2
  simp only [Rat.cast_ofScientific] at hu
  have hl : 12.5 ≤ Real.log (r ^ 2) := by
    rw [Real.log_pow, Nat.cast_ofNat]
    linarith only [hlog]
  have hh : Real.log (r ^ 2) ≤ 12.7 := by
    rw [Real.log_pow, Nat.cast_ofNat]
    linarith only [hu, Real.log_le_log hr₀ hr.2]
  let v := Real.log (r ^ 2) - 23 / 2
  have hv₀ : 0 ≤ v := by
    dsimp only [v]; linarith only [hl]
  have hv₁ : v ≤ 1.2 := by
    dsimp only [v]; linarith only [hh]
  have hv₂ : v ^ 2 ≤ v * 1.2 := by
    rw [pow_two]
    exact mul_le_mul_of_nonneg_left hv₁ hv₀
  have hpoly :
    (4.028663 - 7.025619 * (v + 5 / 3) + 2.061371 * (v ^ 2 + (10 / 3) * v + 50 / 9)) / (3 / 5) ≤
      (10.925 : ℝ) := by
    linarith only [hv₁, hv₂]
  refine (gaussian_profile_main_upper_197 hx (by linarith only [hl])).trans ?_
  refine (mul_le_mul_of_nonneg_left hpoly (Real.rpow_nonneg (sq_nonneg r) _)).trans ?_
  exact
    (mul_le_mul_of_nonneg_right (main_power_to572 hr.1) (by norm_num only : (0 : ℝ) ≤ 10.925)).trans
      (by norm_num only)

/-- Combine the signed density integral, boundary, and Abel error into
one upper bound for substitution in the K197 comparison through radius 572. -/
theorem gaussian_abel_tail_to572 {r : ℝ} (hr : r ∈ Set.Icc 521.25 572) :
    let x := r ^ 2
    (∫ t in Set.Ioi x, gaussianDensity197 t) - (Chebyshev.psi x - x) * gaussianDensity197 x +
        gaussianAbelError197 x ≤
      0.006305 := by
  intro x
  have hp : 0 < r := (by norm_num only : (0 : ℝ) < 521.25).trans_le hr.1
  have hL : (270000 : ℝ) ≤ x :=
    (by norm_num only : (270000 : ℝ) ≤ 521.25 ^ 2).trans
      (pow_le_pow_left₀ (by norm_num only) hr.1 2)
  have hU : x ≤ 572 ^ 2 := pow_le_pow_left₀ hp.le hr.2 2
  have hlog : Real.log x ∈ Set.Icc 11.5 12.7 := by
    have h :=
      (Analysis.rationalLogIntervalCheck_sound (N := 572) (j := 9) (n := 27) (lo := 5) (hi := 6.35)
          (by decide +kernel)).2
    simp only [Rat.cast_ofScientific] at h
    dsimp only [x]
    rw [Real.log_pow, Nat.cast_ofNat]
    have hleft := radius_log_lower ((by norm_num only : (332.15 : ℝ) ≤ 521.25).trans hr.1)
    exact ⟨by linarith only [hleft], by linarith only [h, Real.log_le_log hp hr.2]⟩
  have hmain := gaussian_profile_main_to572 hr
  have hb := gaussian_abel_boundary_to572 hL hU hlog
  have he :=
    gaussian_abel_error_early_197 ((by norm_num only : (110000 : ℝ) ≤ 270000).trans hL)
      (hU.trans (by norm_num only))
  dsimp only [x] at hb he ⊢
  linarith only [hmain, hb, he]

/-- The two overlapping Abel estimates give the same tail bound at every
radius from 336.8 through 572. -/
theorem gaussian_abel_tail_through572 {r : ℝ} (hr : r ∈ Set.Icc 336.8 572) :
    let x := r ^ 2
    (∫ t in Set.Ioi x, gaussianDensity197 t) - (Chebyshev.psi x - x) * gaussianDensity197 x +
        gaussianAbelError197 x ≤
      0.006305 := by
  by_cases hm : r ≤ 522
  · exact gaussian_abel_tail_through522 ⟨hr.1, hm⟩
  · exact
      gaussian_abel_tail_to572
        ⟨(by norm_num only : (521.25 : ℝ) ≤ 522).trans (le_of_not_ge hm), hr.2⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
