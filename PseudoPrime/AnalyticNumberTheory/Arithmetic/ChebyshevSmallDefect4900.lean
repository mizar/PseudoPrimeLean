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

/-! # A small-range higher-prime-power bound through 4900 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- A kernel-checked integer comparison proves `psi 70 ≤ 66.55`. -/
theorem psi_seventy_le_6655 : Chebyshev.psi 70 ≤ (6655 / 100 : ℝ) := by
  have hl : 2 ^ 95 ≤ Nat.lcmUpto 70 := by decide +kernel
  have hu : Nat.lcmUpto 70 ≤ 2 ^ (95 + 1) := by decide +kernel
  have h := psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  linarith only [h.2, Real.log_two_lt_d9]

/-- For `0 ≤ x ≤ 4900`, the square-root psi contribution is at most 66.55. -/
theorem psi_square_root_le_6655_4900 {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 4900) :
    Chebyshev.psi (x ^ ((2 : ℝ)⁻¹)) ≤ (6655 / 100 : ℝ) := by
  apply (Chebyshev.psi_mono _).trans psi_seventy_le_6655
  apply
    (Real.rpow_inv_le_iff_of_pos hx0 (by norm_num only : (0 : ℝ) ≤ 70)
        (by norm_num only : (0 : ℝ) < 2)).2
  norm_num only [Real.rpow_ofNat]
  exact hx

/-- For `0 ≤ x ≤ 4900`, the higher prime-power mass is at most 87.35.
The Costa-Pereira inequality reduces the claim to three checked psi prefixes. -/
theorem psi_sub_theta_le_8735 {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 4900) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (8735 / 100 : ℝ) := by
  have h := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi x
  linarith only [h, psi_square_root_le_6655_4900 hx0 hx,
    psi_cube_root_le_1664 hx0 (hx.trans (by norm_num only)),
    psi_fifth_root_le_416 hx0 (hx.trans (by norm_num only))]

end PseudoPrime.AnalyticNumberTheory.Arithmetic
