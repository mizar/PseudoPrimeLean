/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevLcmBounds
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.SmallDefect.ChebyshevSmallPsiBounds

/-! # A small-range higher-prime-power bound through 5625 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- A kernel-checked least-common-multiple comparison proves `psi 18 ≤ 16.64`. -/
theorem psi_eighteen_le_1664 : Chebyshev.psi 18 ≤ (1664 / 100 : ℝ) := by
  have hl : 2 ^ 23 ≤ Nat.lcmUpto 18 := by decide +kernel
  have hu : Nat.lcmUpto 18 ≤ 2 ^ (23 + 1) := by decide +kernel
  have h := psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  linarith only [h.2, Real.log_two_lt_d9]

/-- A kernel-checked least-common-multiple comparison proves `psi 75 ≤ 75.56`. -/
theorem psi_seventy_five_le_7556 : Chebyshev.psi 75 ≤ (7556 / 100 : ℝ) := by
  have hl : 2 ^ 108 ≤ Nat.lcmUpto 75 := by decide +kernel
  have hu : Nat.lcmUpto 75 ≤ 2 ^ (108 + 1) := by decide +kernel
  have h := psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  linarith only [h.2, Real.log_two_lt_d9]

/-- For `0 ≤ x ≤ 5832`, the cube-root psi contribution is at most 16.64. -/
theorem psi_cube_root_le_1664_5832 {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 5832) :
    Chebyshev.psi (x ^ ((3 : ℝ)⁻¹)) ≤ (1664 / 100 : ℝ) := by
  apply (Chebyshev.psi_mono _).trans psi_eighteen_le_1664
  apply
    (Real.rpow_inv_le_iff_of_pos hx0 (by norm_num only : (0 : ℝ) ≤ 18)
        (by norm_num only : (0 : ℝ) < 3)).2
  norm_num only [Real.rpow_ofNat]
  exact hx

/-- For `0 ≤ x ≤ 5625`, the square-root psi contribution is at most 75.56. -/
theorem psi_square_root_le_7556 {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 5625) :
    Chebyshev.psi (x ^ ((2 : ℝ)⁻¹)) ≤ (7556 / 100 : ℝ) := by
  apply (Chebyshev.psi_mono _).trans psi_seventy_five_le_7556
  apply
    (Real.rpow_inv_le_iff_of_pos hx0 (by norm_num only : (0 : ℝ) ≤ 75)
        (by norm_num only : (0 : ℝ) < 2)).2
  norm_num only [Real.rpow_ofNat]
  exact hx

/-- For `0 ≤ x ≤ 5625`, the higher-prime-power contribution is at most 96.36.
The Costa-Pereira inequality reduces the estimate to three checked psi prefixes. -/
theorem psi_sub_theta_le_9636 {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 5625) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (9636 / 100 : ℝ) := by
  have h := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi x
  linarith only [h, psi_square_root_le_7556 hx0 hx,
    psi_cube_root_le_1664_5832 hx0 (hx.trans (by norm_num only)),
    psi_fifth_root_le_416 hx0 (hx.trans (by norm_num only))]

end PseudoPrime.AnalyticNumberTheory.Arithmetic
