/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevLcmBounds

/-! # A small-range higher-prime-power bound through 16384 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- A kernel-checked least-common-multiple comparison proves `psi 7 ≤ 6.24`. -/
theorem psi_seven_le_624 : Chebyshev.psi 7 ≤ (624 / 100 : ℝ) := by
  have hl : 2 ^ 8 ≤ Nat.lcmUpto 7 := by decide +kernel
  have hu : Nat.lcmUpto 7 ≤ 2 ^ (8 + 1) := by decide +kernel
  have h := psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  linarith only [h.2, Real.log_two_lt_d9]

/-- A kernel-checked least-common-multiple comparison proves `psi 26 ≤ 24.27`. -/
theorem psi_twenty_six_le_2427 : Chebyshev.psi 26 ≤ (2427 / 100 : ℝ) := by
  have hl : 2 ^ 34 ≤ Nat.lcmUpto 26 := by decide +kernel
  have hu : Nat.lcmUpto 26 ≤ 2 ^ (34 + 1) := by decide +kernel
  have h := psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  linarith only [h.2, Real.log_two_lt_d9]

/-- A kernel-checked least-common-multiple comparison proves `psi 128 ≤ 127.55`. -/
theorem psi_one_twenty_eight_le_12755 : Chebyshev.psi 128 ≤ (12755 / 100 : ℝ) := by
  have hl : 2 ^ 183 ≤ Nat.lcmUpto 128 := by decide +kernel
  have hu : Nat.lcmUpto 128 ≤ 2 ^ (183 + 1) := by decide +kernel
  have h := psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  linarith only [h.2, Real.log_two_lt_d9]

/-- For `0 ≤ x ≤ 16807`, the fifth-root psi contribution is at most 6.24. -/
theorem psi_fifth_root_le_624 {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 16807) :
    Chebyshev.psi (x ^ ((5 : ℝ)⁻¹)) ≤ (624 / 100 : ℝ) := by
  apply (Chebyshev.psi_mono _).trans psi_seven_le_624
  apply
    (Real.rpow_inv_le_iff_of_pos hx0 (by norm_num only : (0 : ℝ) ≤ 7)
        (by norm_num only : (0 : ℝ) < 5)).2
  norm_num only [Real.rpow_ofNat]
  exact hx

/-- For `0 ≤ x ≤ 17576`, the cube-root psi contribution is at most 24.27. -/
theorem psi_cube_root_le_2427 {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 17576) :
    Chebyshev.psi (x ^ ((3 : ℝ)⁻¹)) ≤ (2427 / 100 : ℝ) := by
  apply (Chebyshev.psi_mono _).trans psi_twenty_six_le_2427
  apply
    (Real.rpow_inv_le_iff_of_pos hx0 (by norm_num only : (0 : ℝ) ≤ 26)
        (by norm_num only : (0 : ℝ) < 3)).2
  norm_num only [Real.rpow_ofNat]
  exact hx

/-- For `0 ≤ x ≤ 16384`, the square-root psi contribution is at most 127.55. -/
theorem psi_square_root_le_12755 {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 16384) :
    Chebyshev.psi (x ^ ((2 : ℝ)⁻¹)) ≤ (12755 / 100 : ℝ) := by
  apply (Chebyshev.psi_mono _).trans psi_one_twenty_eight_le_12755
  apply
    (Real.rpow_inv_le_iff_of_pos hx0 (by norm_num only : (0 : ℝ) ≤ 128)
        (by norm_num only : (0 : ℝ) < 2)).2
  norm_num only [Real.rpow_ofNat]
  exact hx

/-- For `0 ≤ x ≤ 16384`, the higher-prime-power contribution is at most 158.06.
The Costa-Pereira inequality reduces the estimate to three checked psi prefixes. -/
theorem psi_sub_theta_le_15806 {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 16384) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (15806 / 100 : ℝ) := by
  have h := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi x
  linarith only [h, psi_square_root_le_12755 hx0 hx,
    psi_cube_root_le_2427 hx0 (hx.trans (by norm_num only)),
    psi_fifth_root_le_624 hx0 (hx.trans (by norm_num only))]

end PseudoPrime.AnalyticNumberTheory.Arithmetic
