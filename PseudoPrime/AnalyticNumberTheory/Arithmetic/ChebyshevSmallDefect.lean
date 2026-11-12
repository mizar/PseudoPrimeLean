/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevLcmBounds

/-! # A small-range higher-prime-power bound -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- A kernel-checked integer comparison proves `psi 4 ≤ 2.8`. -/
theorem psi_four_le_280 : Chebyshev.psi 4 ≤ (28 / 10 : ℝ) := by
  have hl : 2 ^ 3 ≤ Nat.lcmUpto 4 := by decide +kernel
  have hu : Nat.lcmUpto 4 ≤ 2 ^ (3 + 1) := by decide +kernel
  have h := psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  linarith only [h.2, Real.log_two_lt_d9]

/-- A kernel-checked integer comparison proves `psi 14 ≤ 13.2`. -/
theorem psi_fourteen_le_1320 : Chebyshev.psi 14 ≤ (132 / 10 : ℝ) := by
  have hl : 2 ^ 18 ≤ Nat.lcmUpto 14 := by decide +kernel
  have hu : Nat.lcmUpto 14 ≤ 2 ^ (18 + 1) := by decide +kernel
  have h := psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  linarith only [h.2, Real.log_two_lt_d9]

/-- A kernel-checked integer comparison proves `psi 52 ≤ 49.91`. -/
theorem psi_fifty_two_le_4991 : Chebyshev.psi 52 ≤ (4991 / 100 : ℝ) := by
  have hl : 2 ^ 71 ≤ Nat.lcmUpto 52 := by decide +kernel
  have hu : Nat.lcmUpto 52 ≤ 2 ^ (71 + 1) := by decide +kernel
  have h := psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  linarith only [h.2, Real.log_two_lt_d9]

/-- For `0 ≤ x ≤ 2704`, the fifth-root psi contribution is at most 2.8. -/
theorem psi_fifth_root_le_280_2704 {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 2704) :
    Chebyshev.psi (x ^ ((5 : ℝ)⁻¹)) ≤ (28 / 10 : ℝ) := by
  have hr : x ^ ((5 : ℝ)⁻¹) ≤ (49 / 10 : ℝ) := by
    apply
      (Real.rpow_inv_le_iff_of_pos hx0 (by norm_num only : (0 : ℝ) ≤ 49 / 10)
          (by norm_num only : (0 : ℝ) < 5)).2
    norm_num only [Real.rpow_ofNat]
    linarith only [hx]
  have hf : ⌊(49 / 10 : ℝ)⌋₊ = 4 :=
    (Nat.floor_eq_iff (by norm_num only)).2 (by norm_num only [and_self])
  have he : Chebyshev.psi (49 / 10 : ℝ) = Chebyshev.psi 4 := by
    rw [Chebyshev.psi_eq_psi_coe_floor, hf]
    norm_num only [Nat.cast_ofNat]
  exact (Chebyshev.psi_mono hr).trans (he ▸ psi_four_le_280)

/-- For `0 ≤ x ≤ 2704`, the cube-root psi contribution is at most 13.2. -/
theorem psi_cube_root_le_1320_2704 {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 2704) :
    Chebyshev.psi (x ^ ((3 : ℝ)⁻¹)) ≤ (132 / 10 : ℝ) := by
  apply (Chebyshev.psi_mono _).trans psi_fourteen_le_1320
  apply
    (Real.rpow_inv_le_iff_of_pos hx0 (by norm_num only : (0 : ℝ) ≤ 14)
        (by norm_num only : (0 : ℝ) < 3)).2
  norm_num only [Real.rpow_ofNat]
  linarith only [hx]

/-- For `0 ≤ x ≤ 2704`, the square-root psi contribution is at most 49.91. -/
theorem psi_square_root_le_4991_2704 {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 2704) :
    Chebyshev.psi (x ^ ((2 : ℝ)⁻¹)) ≤ (4991 / 100 : ℝ) := by
  apply (Chebyshev.psi_mono _).trans psi_fifty_two_le_4991
  apply
    (Real.rpow_inv_le_iff_of_pos hx0 (by norm_num only : (0 : ℝ) ≤ 52)
        (by norm_num only : (0 : ℝ) < 2)).2
  norm_num only [Real.rpow_ofNat]
  exact hx

/-- For `0 ≤ x ≤ 2704`, the higher prime-power mass is at most 65.91.
The Costa-Pereira inequality reduces it to three checked small psi prefixes. -/
theorem psi_sub_theta_le_6591 {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 2704) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (6591 / 100 : ℝ) := by
  have h := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi x
  linarith only [h, psi_square_root_le_4991_2704 hx0 hx, psi_cube_root_le_1320_2704 hx0 hx,
    psi_fifth_root_le_280_2704 hx0 hx]

end PseudoPrime.AnalyticNumberTheory.Arithmetic
