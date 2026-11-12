/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevLcmBounds

/-! # A small-range higher-prime-power bound through 32768 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- A kernel-checked least-common-multiple comparison proves `psi 8 ≤ 6.94`. -/
theorem psi_eight_le_694 : Chebyshev.psi 8 ≤ (694 / 100 : ℝ) := by
  have hl : 2 ^ 9 ≤ Nat.lcmUpto 8 := by decide +kernel
  have hu : Nat.lcmUpto 8 ≤ 2 ^ (9 + 1) := by decide +kernel
  have h := psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  linarith only [h.2, Real.log_two_lt_d9]

/-- A kernel-checked least-common-multiple comparison proves `psi 32 ≤ 33.28`. -/
theorem psi_thirty_two_le_3328 : Chebyshev.psi 32 ≤ (3328 / 100 : ℝ) := by
  have hl : 2 ^ 47 ≤ Nat.lcmUpto 32 := by decide +kernel
  have hu : Nat.lcmUpto 32 ≤ 2 ^ (47 + 1) := by decide +kernel
  have h := psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  linarith only [h.2, Real.log_two_lt_d9]

/-- A kernel-checked least-common-multiple comparison proves `psi 182 ≤ 185.08`. -/
theorem psi_one_eighty_two_le_18508 : Chebyshev.psi 182 ≤ (18508 / 100 : ℝ) := by
  have hl : 2 ^ 266 ≤ Nat.lcmUpto 182 := by decide +kernel
  have hu : Nat.lcmUpto 182 ≤ 2 ^ (266 + 1) := by decide +kernel
  have h := psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  linarith only [h.2, Real.log_two_lt_d9]

/-- For `0 ≤ x ≤ 32768`, the fifth-root psi contribution is at most 6.94. -/
theorem psi_fifth_root_le_694 {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 32768) :
    Chebyshev.psi (x ^ ((5 : ℝ)⁻¹)) ≤ (694 / 100 : ℝ) := by
  apply (Chebyshev.psi_mono _).trans psi_eight_le_694
  apply
    (Real.rpow_inv_le_iff_of_pos hx0 (by norm_num only : (0 : ℝ) ≤ 8)
        (by norm_num only : (0 : ℝ) < 5)).2
  norm_num only [Real.rpow_ofNat]
  exact hx

/-- For `0 ≤ x ≤ 32768`, the cube-root psi contribution is at most 33.28. -/
theorem psi_cube_root_le_3328 {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 32768) :
    Chebyshev.psi (x ^ ((3 : ℝ)⁻¹)) ≤ (3328 / 100 : ℝ) := by
  apply (Chebyshev.psi_mono _).trans psi_thirty_two_le_3328
  apply
    (Real.rpow_inv_le_iff_of_pos hx0 (by norm_num only : (0 : ℝ) ≤ 32)
        (by norm_num only : (0 : ℝ) < 3)).2
  norm_num only [Real.rpow_ofNat]
  exact hx

/-- For `0 ≤ x ≤ 32768`, the square-root psi contribution is at most 185.08. -/
theorem psi_square_root_le_18508 {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 32768) :
    Chebyshev.psi (x ^ ((2 : ℝ)⁻¹)) ≤ (18508 / 100 : ℝ) := by
  apply (Chebyshev.psi_mono _).trans psi_one_eighty_two_le_18508
  apply
    (Real.rpow_inv_le_iff_of_pos hx0 (by norm_num only : (0 : ℝ) ≤ 182)
        (by norm_num only : (0 : ℝ) < 2)).2
  norm_num only [Real.rpow_ofNat]
  exact hx.trans (by norm_num only)

/-- For `0 ≤ x ≤ 32768`, the higher-prime-power contribution is at most 225.30.
The Costa-Pereira inequality reduces the estimate to three checked psi prefixes. -/
theorem psi_sub_theta_le_22530 {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 32768) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (22530 / 100 : ℝ) := by
  have h := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi x
  linarith only [h, psi_square_root_le_18508 hx0 hx,
    psi_cube_root_le_3328 hx0 (hx.trans (by norm_num only)),
    psi_fifth_root_le_694 hx0 (hx.trans (by norm_num only))]

end PseudoPrime.AnalyticNumberTheory.Arithmetic
