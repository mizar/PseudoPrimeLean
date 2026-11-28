/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197PowerBounds
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197PowerBounds
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Profile

/-! # The K197 Abel tail through radius 354 -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private theorem profile_boundary_abs_to354 {v : ℝ} (hv : v ∈ Set.Icc 11.5 11.74) :
    |gaussianProfile197 v| ≤ 5 := by
  rw [profile_expand_197, abs_le]
  have hz : 0 ≤ v - 23 / 2 := by linarith only [hv.1]
  have hU : v - 23 / 2 ≤ 0.24 := by linarith only [hv.2]
  have hsq := pow_le_pow_left₀ hz hU 2
  have h := profile_coeff_bounds_197
  have h₀ := mul_le_mul_of_nonneg_right h.2.1.1 hz
  have h₁ := mul_le_mul_of_nonneg_right h.2.1.2 hz
  have h₂ := mul_le_mul_of_nonneg_right h.2.2.1 (sq_nonneg (v - 23 / 2))
  have h₃ := mul_le_mul_of_nonneg_right h.2.2.2 (sq_nonneg (v - 23 / 2))
  exact
    ⟨by linarith only [h.1.1, h₀, h₂, hz, hU, sq_nonneg (v - 23 / 2)], by
      linarith only [h.1.2, h₁, h₃, hz, hsq]⟩

/-- On the squared cutoffs from radius 336.8 to 354 the finite Chebyshev envelope
and the signed profile box bound the remaining Abel boundary term. -/
theorem gaussian_abel_boundary_to354 {x : ℝ} (hx : 110000 ≤ x) (hU : x ≤ 354 ^ 2)
    (hl : Real.log x ∈ Set.Icc 11.5 11.74) :
    -(Chebyshev.psi x - x) * gaussianDensity197 x ≤ 0.000013 := by
  have hxp : 0 ≤ x := (by norm_num only : (0 : ℝ) ≤ 110000).trans hx
  have hψ :=
    AnalyticNumberTheory.Arithmetic.psi_four_fifths_1423_million
      ((by norm_num only : (1423 : ℝ) ≤ 110000).trans hx) (hU.trans (by norm_num only))
  have hs : Real.sqrt x ≤ 354 := (Real.sqrt_le_iff).mpr ⟨by norm_num only, hU⟩
  have he : |Chebyshev.psi x - x| ≤ (283.2 : ℝ) := by linarith only [hψ, hs]
  have hd : |gaussianDensity197 x| ≤ (0.000000045 : ℝ) := by
    rw [gaussianDensity197, abs_mul, abs_of_nonneg (Real.rpow_nonneg hxp _)]
    have h :=
      mul_le_mul (boundary_power_bound hx) (profile_boundary_abs_to354 hl) (abs_nonneg _)
        (by norm_num only)
    linarith only [h]
  have h := mul_le_mul he hd (abs_nonneg _) (by norm_num only)
  have hh := le_abs_self (-(Chebyshev.psi x - x) * gaussianDensity197 x)
  rw [abs_mul, abs_neg] at hh
  linarith only [h, hh]

/-- The signed main integral costs at most 0.006 on the K197 radii from 336.8 to 354.
This bounds the combined quadratic before multiplying by the positive power. -/
theorem gaussian_profile_main_to354 {r : ℝ} (hr : r ∈ Set.Icc 336.8 354) :
    (∫ t in Set.Ioi (r ^ 2), gaussianDensity197 t) ≤ 0.006 := by
  have hr₀ : 0 < r := (by norm_num only : (0 : ℝ) < 336.8).trans_le hr.1
  have hx : 1 ≤ r ^ 2 := one_le_pow₀ ((by norm_num only : (1 : ℝ) ≤ 336.8).trans hr.1)
  have hlog := radius_log_lower ((by norm_num only : (332.15 : ℝ) ≤ 336.8).trans hr.1)
  have hu :=
    (Analysis.rationalLogIntervalCheck_sound (N := 354) (j := 9) (n := 27) (lo := 5) (hi := 5.87)
        (by decide +kernel)).2
  simp only [Rat.cast_ofScientific] at hu
  have hl : 11.611 ≤ Real.log (r ^ 2) := by
    rw [Real.log_pow, Nat.cast_ofNat]
    linarith only [hlog]
  have hh : Real.log (r ^ 2) ≤ 11.74 := by
    rw [Real.log_pow, Nat.cast_ofNat]
    linarith only [hu, Real.log_le_log hr₀ hr.2]
  let v := Real.log (r ^ 2) - 23 / 2
  have hv₀ : 0 ≤ v := by
    dsimp only [v]; linarith only [hl]
  have hvlo : 0.111 ≤ v := by
    dsimp only [v]; linarith only [hl]
  have hv₁ : v ≤ 0.24 := by
    dsimp only [v]; linarith only [hh]
  have hv₂ := pow_le_pow_left₀ hv₀ hv₁ 2
  have hpoly :
    (4.028663 - 7.025619 * (v + 5 / 3) + 2.061371 * (v ^ 2 + (10 / 3) * v + 50 / 9)) / (3 / 5) ≤
      (6.46 : ℝ) := by
    linarith only [hvlo, hv₂]
  refine (gaussian_profile_main_upper_197 hx (by linarith only [hl])).trans ?_
  refine (mul_le_mul_of_nonneg_left hpoly (Real.rpow_nonneg (sq_nonneg r) _)).trans ?_
  exact
    (mul_le_mul_of_nonneg_right (mid_main_power hr.1) (by norm_num only : (0 : ℝ) ≤ 6.46)).trans
      (by norm_num only)

/-- Combine the signed density integral, boundary, and Abel error into
one upper bound for substitution in the K197 comparison through radius 354. -/
theorem gaussian_abel_tail_to354 {r : ℝ} (hr : r ∈ Set.Icc 336.8 354) :
    let x := r ^ 2
    (∫ t in Set.Ioi x, gaussianDensity197 t) - (Chebyshev.psi x - x) * gaussianDensity197 x +
        gaussianAbelError197 x ≤
      0.006305 := by
  intro x
  have hp : 0 < r := (by norm_num only : (0 : ℝ) < 336.8).trans_le hr.1
  have hL : (110000 : ℝ) ≤ x :=
    (by norm_num only : (110000 : ℝ) ≤ 336.8 ^ 2).trans (pow_le_pow_left₀ (by norm_num only) hr.1 2)
  have hU : x ≤ 354 ^ 2 := pow_le_pow_left₀ hp.le hr.2 2
  have hlog : Real.log x ∈ Set.Icc 11.5 11.74 := by
    have h :=
      (Analysis.rationalLogIntervalCheck_sound (N := 354) (j := 9) (n := 27) (lo := 5) (hi := 5.87)
          (by decide +kernel)).2
    simp only [Rat.cast_ofScientific] at h
    dsimp only [x]
    rw [Real.log_pow, Nat.cast_ofNat]
    have hleft := radius_log_lower ((by norm_num only : (332.15 : ℝ) ≤ 336.8).trans hr.1)
    exact ⟨by linarith only [hleft], by linarith only [h, Real.log_le_log hp hr.2]⟩
  have hmain := gaussian_profile_main_to354 hr
  have hb := gaussian_abel_boundary_to354 hL hU hlog
  have he := gaussian_abel_error_early_197 hL (hU.trans (by norm_num only))
  dsimp only [x] at hb he ⊢
  linarith only [hmain, hb, he]

end PseudoPrime.PrimeTestBounds.MillerRabin
