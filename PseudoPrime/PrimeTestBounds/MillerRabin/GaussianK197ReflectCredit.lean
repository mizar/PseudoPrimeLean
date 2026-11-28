/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterBridgeReflect663
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterBridgeReflect663

/-! # Retained principal reflected Euler credit on the early K197 radii -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private theorem k197_reflect_geometry {r : ℝ} (hr : r ∈ Set.Icc 328 337) :
    14.21 ≤ 21 / 8 + Real.log (r ^ 2) ∧
      0.000000153 ≤ Real.exp (-(11 / 10) * (21 / 8 + Real.log (r ^ 2))) := by
  have h₀ := (by norm_num only : (0 : ℝ) < 328).trans_le hr.1
  have hl :=
    (Analysis.rationalLogIntervalCheck_sound (N := 328) (j := 9) (n := 27) (lo := 5.793) (hi := 6)
        (by decide +kernel)).1
  have hu :=
    (Analysis.rationalLogIntervalCheck_sound (N := 337) (j := 9) (n := 27) (lo := 5) (hi := 5.82009)
        (by decide +kernel)).2
  have he :=
    (Analysis.rationalLogIntervalCheck_sound (N := 1000000000 / 153) (j := 23) (n := 32) (lo :=
        15.6917) (hi := 16) (by decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div, Rat.cast_ofScientific] at hl hu he
  have hz : 14.21 ≤ 21 / 8 + Real.log (r ^ 2) := by
    rw [Real.log_pow]
    linarith only [hl, Real.log_le_log (by norm_num only : (0 : ℝ) < 328) hr.1]
  have hd : 0.000000153 ≤ Real.exp (-(11 / 10) * (21 / 8 + Real.log (r ^ 2))) := by
    apply (Real.log_le_iff_le_exp (by norm_num only)).mp
    have hi : Real.log (0.000000153 : ℝ)⁻¹ ≥ 15.6917 := by
      norm_num only at he ⊢; exact he
    rw [Real.log_inv] at hi
    rw [Real.log_pow]
    linarith only [hi, hu, Real.log_le_log h₀ hr.2]
  exact ⟨hz, hd⟩

private theorem reflect_credit_of_exp {r D C : ℝ} (hr : 328 ≤ r)
    (hz : 14.21 ≤ 21 / 8 + Real.log (r ^ 2))
    (hd : D ≤ Real.exp (-(11 / 10) * (21 / 8 + Real.log (r ^ 2))))
    (hC : C ≤ (11 / 10) ^ 5 / 40 * 1485000 * D) :
    C ≤ 3 * quarterMainEuler656 (1 : DirichletCharacter ℂ 1) (r ^ 2) := by
  have hx : 1 ≤ r ^ 2 := one_le_pow₀ ((by norm_num only : (1 : ℝ) ≤ 328).trans hr)
  have h := principal_reflect_prefix_656 hx
  have hprod :=
    mul_le_mul hd (bridge_reflect_moment_lower hz) (by norm_num only : (0 : ℝ) ≤ 1485000)
      (Real.exp_pos _).le
  rw [Real.rpow_def_of_pos (zero_lt_one.trans_le hx)] at h
  rw [show
      -(11 / 10 : ℝ) * (21 / 8 + Real.log (r ^ 2)) =
        -(11 / 10) * (21 / 8) + Real.log (r ^ 2) * -(11 / 10)
      by ring,
    Real.exp_add] at hprod
  nlinarith only [h, hprod, hC]

/-- The prefix through 2701 gives a uniform lower bound for three copies
of the principal reflected Euler series through radius 337. -/
theorem gaussian_k197_reflect_credit {r : ℝ} (hr : r ∈ Set.Icc 328 337) :
    0.00914 ≤ 3 * quarterMainEuler656 (1 : DirichletCharacter ℂ 1) (r ^ 2) := by
  obtain ⟨hz, hd⟩ := k197_reflect_geometry hr
  exact reflect_credit_of_exp hr.1 hz hd (by norm_num only)

private theorem k197_mid_reflect_geometry {r : ℝ} (hr : r ∈ Set.Icc 328 342.9) :
    14.21 ≤ 21 / 8 + Real.log (r ^ 2) ∧
      0.000000147 ≤ Real.exp (-(11 / 10) * (21 / 8 + Real.log (r ^ 2))) := by
  have h₀ := (by norm_num only : (0 : ℝ) < 328).trans_le hr.1
  have hl :=
    (Analysis.rationalLogIntervalCheck_sound (N := 328) (j := 9) (n := 27) (lo := 5.793) (hi := 6)
        (by decide +kernel)).1
  have hu :=
    (Analysis.rationalLogIntervalCheck_sound (N := 342.9) (j := 9) (n := 27) (lo := 5) (hi := 5.838)
        (by decide +kernel)).2
  have he :=
    (Analysis.rationalLogIntervalCheck_sound (N := 1000000000 / 147) (j := 23) (n := 32) (lo :=
        15.7328) (hi := 16) (by decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div, Rat.cast_ofScientific] at hl hu he
  have hz : 14.21 ≤ 21 / 8 + Real.log (r ^ 2) := by
    rw [Real.log_pow]
    linarith only [hl, Real.log_le_log (by norm_num only : (0 : ℝ) < 328) hr.1]
  have hru : r ≤ (3429 / 10 : ℝ) := by linarith only [hr.2]
  have hd : 0.000000147 ≤ Real.exp (-(11 / 10) * (21 / 8 + Real.log (r ^ 2))) := by
    apply (Real.log_le_iff_le_exp (by norm_num only)).mp
    have hi : Real.log (0.000000147 : ℝ)⁻¹ ≥ 15.7328 := by
      norm_num only at he ⊢; exact he
    rw [Real.log_inv] at hi
    rw [Real.log_pow]
    linarith only [hi, hu, Real.log_le_log h₀ hru]
  exact ⟨hz, hd⟩

/-- The prefix through 2701 gives a uniform lower bound for three copies
of the principal reflected Euler series through radius 342.9. -/
theorem gaussian_k197_mid_reflect_credit {r : ℝ} (hr : r ∈ Set.Icc 328 342.9) :
    0.00878 ≤ 3 * quarterMainEuler656 (1 : DirichletCharacter ℂ 1) (r ^ 2) := by
  obtain ⟨hz, hd⟩ := k197_mid_reflect_geometry hr
  exact reflect_credit_of_exp hr.1 hz hd (by norm_num only)

private theorem k197_reflect_to34610 {r : ℝ} (hr : r ∈ Set.Icc 328 346.1) :
    14.21 ≤ 21 / 8 + Real.log (r ^ 2) ∧
      0.000000144 ≤ Real.exp (-(11 / 10) * (21 / 8 + Real.log (r ^ 2))) := by
  have h₀ := (by norm_num only : (0 : ℝ) < 328).trans_le hr.1
  have hl :=
    (Analysis.rationalLogIntervalCheck_sound (N := 328) (j := 9) (n := 27) (lo := 5.793) (hi := 6)
        (by decide +kernel)).1
  have hu :=
    (Analysis.rationalLogIntervalCheck_sound (N := 346.1) (j := 9) (n := 27) (lo := 5) (hi := 5.847)
        (by decide +kernel)).2
  have he :=
    (Analysis.rationalLogIntervalCheck_sound (N := 1000000000 / 144) (j := 23) (n := 32) (lo :=
        15.7534) (hi := 16) (by decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div, Rat.cast_ofScientific] at hl hu he
  have hz : 14.21 ≤ 21 / 8 + Real.log (r ^ 2) := by
    rw [Real.log_pow]
    linarith only [hl, Real.log_le_log (by norm_num only : (0 : ℝ) < 328) hr.1]
  have hru : r ≤ (3461 / 10 : ℝ) := by linarith only [hr.2]
  have hd : 0.000000144 ≤ Real.exp (-(11 / 10) * (21 / 8 + Real.log (r ^ 2))) := by
    apply (Real.log_le_iff_le_exp (by norm_num only)).mp
    have hi : Real.log (0.000000144 : ℝ)⁻¹ ≥ 15.7534 := by
      norm_num only at he ⊢; exact he
    rw [Real.log_inv] at hi
    rw [Real.log_pow]
    linarith only [hi, hu, Real.log_le_log h₀ hru]
  exact ⟨hz, hd⟩

/-- The prefix through 2701 gives a uniform lower bound for three copies
of the principal reflected Euler series through radius 346.1. -/
theorem gaussian_k197_reflect_credit_to34610 {r : ℝ} (hr : r ∈ Set.Icc 328 346.1) :
    0.0086 ≤ 3 * quarterMainEuler656 (1 : DirichletCharacter ℂ 1) (r ^ 2) := by
  obtain ⟨hz, hd⟩ := k197_reflect_to34610 hr
  exact reflect_credit_of_exp hr.1 hz hd (by norm_num only)

end PseudoPrime.PrimeTestBounds.MillerRabin
