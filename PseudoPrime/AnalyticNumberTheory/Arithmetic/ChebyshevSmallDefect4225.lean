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

/-! # A small-range higher-prime-power bound through 4225 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- A kernel-checked integer comparison proves `psi 65 ≤ 62.39`. -/
theorem psi_sixty_five_le_6239 : Chebyshev.psi 65 ≤ (6239 / 100 : ℝ) := by
  have hl : 2 ^ 89 ≤ Nat.lcmUpto 65 := by decide +kernel
  have hu : Nat.lcmUpto 65 ≤ 2 ^ (89 + 1) := by decide +kernel
  have h := psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  linarith only [h.2, Real.log_two_lt_d9]

/-- For `0 ≤ x ≤ 4225`, the square-root psi contribution is at most 62.39. -/
theorem psi_square_root_le_6239_4225 {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 4225) :
    Chebyshev.psi (x ^ ((2 : ℝ)⁻¹)) ≤ (6239 / 100 : ℝ) := by
  apply (Chebyshev.psi_mono _).trans psi_sixty_five_le_6239
  apply
    (Real.rpow_inv_le_iff_of_pos hx0 (by norm_num only : (0 : ℝ) ≤ 65)
        (by norm_num only : (0 : ℝ) < 2)).2
  norm_num only [Real.rpow_ofNat]
  exact hx

/-- For `0 ≤ x ≤ 4225`, the higher prime-power mass is at most 83.19.
The Costa-Pereira inequality reduces the claim to three checked psi prefixes. -/
theorem psi_sub_theta_le_8319 {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 4225) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (8319 / 100 : ℝ) := by
  have h := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi x
  linarith only [h, psi_square_root_le_6239_4225 hx0 hx,
    psi_cube_root_le_1664 hx0 (hx.trans (by norm_num only)),
    psi_fifth_root_le_416 hx0 (hx.trans (by norm_num only))]

end PseudoPrime.AnalyticNumberTheory.Arithmetic
