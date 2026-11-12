/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevLcmBounds
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSmallPsiBounds

/-! # A small-range higher-prime-power bound through 7776 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- A kernel-checked least-common-multiple comparison proves `psi 20 ≤ 19.41`. -/
theorem psi_twenty_le_1941 : Chebyshev.psi 20 ≤ (1941 / 100 : ℝ) := by
  have hl : 2 ^ 27 ≤ Nat.lcmUpto 20 := by decide +kernel
  have hu : Nat.lcmUpto 20 ≤ 2 ^ (27 + 1) := by decide +kernel
  have h := psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  linarith only [h.2, Real.log_two_lt_d9]

/-- A kernel-checked least-common-multiple comparison proves `psi 89 ≤ 90.11`. -/
theorem psi_eighty_nine_le_9011 : Chebyshev.psi 89 ≤ (9011 / 100 : ℝ) := by
  have hl : 2 ^ 129 ≤ Nat.lcmUpto 89 := by decide +kernel
  have hu : Nat.lcmUpto 89 ≤ 2 ^ (129 + 1) := by decide +kernel
  have h := psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  linarith only [h.2, Real.log_two_lt_d9]

/-- For `0 ≤ x ≤ 8000`, the cube-root psi contribution is at most 19.41. -/
theorem psi_cube_root_le_1941 {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 8000) :
    Chebyshev.psi (x ^ ((3 : ℝ)⁻¹)) ≤ (1941 / 100 : ℝ) := by
  apply (Chebyshev.psi_mono _).trans psi_twenty_le_1941
  apply
    (Real.rpow_inv_le_iff_of_pos hx0 (by norm_num only : (0 : ℝ) ≤ 20)
        (by norm_num only : (0 : ℝ) < 3)).2
  norm_num only [Real.rpow_ofNat]
  exact hx

/-- For `0 ≤ x ≤ 7921`, the square-root psi contribution is at most 90.11. -/
theorem psi_square_root_le_9011 {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 7921) :
    Chebyshev.psi (x ^ ((2 : ℝ)⁻¹)) ≤ (9011 / 100 : ℝ) := by
  apply (Chebyshev.psi_mono _).trans psi_eighty_nine_le_9011
  apply
    (Real.rpow_inv_le_iff_of_pos hx0 (by norm_num only : (0 : ℝ) ≤ 89)
        (by norm_num only : (0 : ℝ) < 2)).2
  norm_num only [Real.rpow_ofNat]
  exact hx

/-- For `0 ≤ x ≤ 7776`, the higher-prime-power contribution is at most 113.68.
The Costa-Pereira inequality reduces the estimate to three checked psi prefixes. -/
theorem psi_sub_theta_le_11368 {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 7776) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (11368 / 100 : ℝ) := by
  have h := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi x
  linarith only [h, psi_square_root_le_9011 hx0 (hx.trans (by norm_num only)),
    psi_cube_root_le_1941 hx0 (hx.trans (by norm_num only)), psi_fifth_root_le_416 hx0 hx]

end PseudoPrime.AnalyticNumberTheory.Arithmetic
