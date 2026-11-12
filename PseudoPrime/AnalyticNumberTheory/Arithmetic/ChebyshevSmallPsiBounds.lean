/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevLcmBounds

/-! # Shared bounds for small Chebyshev psi prefixes -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- A kernel-checked least-common-multiple comparison bounds `psi 6` by 4.16.
This prefix is shared by finite higher-prime-power estimates. -/
theorem psi_six_le : Chebyshev.psi 6 ≤ (416 / 100 : ℝ) := by
  have hl : 2 ^ 5 ≤ Nat.lcmUpto 6 := by decide +kernel
  have hu : Nat.lcmUpto 6 ≤ 2 ^ (5 + 1) := by decide +kernel
  have h := psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  linarith only [h.2, Real.log_two_lt_d9]

/-- A kernel-checked least-common-multiple comparison bounds `psi 17` by 16.64.
This prefix is shared by finite higher-prime-power estimates. -/
theorem psi_seventeen_le : Chebyshev.psi 17 ≤ (1664 / 100 : ℝ) := by
  have hl : 2 ^ 23 ≤ Nat.lcmUpto 17 := by decide +kernel
  have hu : Nat.lcmUpto 17 ≤ 2 ^ (23 + 1) := by decide +kernel
  have h := psi_bounds_of_lcm_pow_two hl hu
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  linarith only [h.2, Real.log_two_lt_d9]

/-- For `0 ≤ x ≤ 7776`, the fifth-root psi contribution is at most 4.16.
The root is at most 6, where the shared endpoint bound applies. -/
theorem psi_fifth_root_le_416 {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 7776) :
    Chebyshev.psi (x ^ ((5 : ℝ)⁻¹)) ≤ (416 / 100 : ℝ) := by
  apply (Chebyshev.psi_mono _).trans psi_six_le
  apply
    (Real.rpow_inv_le_iff_of_pos hx0 (by norm_num only : (0 : ℝ) ≤ 6)
        (by norm_num only : (0 : ℝ) < 5)).2
  norm_num only [Real.rpow_ofNat]
  exact hx

/-- For `0 ≤ x ≤ 4913`, the cube-root psi contribution is at most 16.64.
The root is at most 17, where the shared endpoint bound applies. -/
theorem psi_cube_root_le_1664 {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 4913) :
    Chebyshev.psi (x ^ ((3 : ℝ)⁻¹)) ≤ (1664 / 100 : ℝ) := by
  apply (Chebyshev.psi_mono _).trans psi_seventeen_le
  apply
    (Real.rpow_inv_le_iff_of_pos hx0 (by norm_num only : (0 : ℝ) ≤ 17)
        (by norm_num only : (0 : ℝ) < 3)).2
  norm_num only [Real.rpow_ofNat]
  exact hx

end PseudoPrime.AnalyticNumberTheory.Arithmetic
