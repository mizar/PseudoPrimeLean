/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevLinearBound
import PseudoPrime.AnalyticNumberTheory.Arithmetic.CompositeMangoldtSqrtBound

/-! # A higher-prime-power bound through 3600 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- For `0 ≤ x ≤ 3600`, the higher-prime-power contribution to `psi x` is at most
91.02. The three-root inequality and the global 1.11 psi bound reduce the claim
to elementary bounds on the square, cube and fifth roots. -/
theorem psi_sub_theta_le_9102 {x : ℝ} (hx : 0 ≤ x) (hu : x ≤ 3600) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (4551 / 50 : ℝ) := by
  have h := psi_sub_theta_le_roots (C := (111 / 100 : ℝ)) hx (fun t ht ↦ psi_le_111 ht)
  have h2 : Real.sqrt x ≤ 60 := by
    have hs := Real.sqrt_le_sqrt (show x ≤ (60 : ℝ) ^ 2 by linarith only [hu])
    rw [Real.sqrt_sq (by norm_num only)] at hs
    exact hs
  have h3 : x ^ (1 / 3 : ℝ) ≤ 16 := by
    rw [one_div]
    apply
      (Real.rpow_inv_le_iff_of_pos hx (by norm_num only : (0 : ℝ) ≤ 16)
          (by norm_num only : (0 : ℝ) < 3)).2
    norm_num only [Real.rpow_ofNat]
    linarith only [hu]
  have h5 : x ^ (1 / 5 : ℝ) ≤ 6 := by
    rw [one_div]
    apply
      (Real.rpow_inv_le_iff_of_pos hx (by norm_num only : (0 : ℝ) ≤ 6)
          (by norm_num only : (0 : ℝ) < 5)).2
    norm_num only [Real.rpow_ofNat]
    linarith only [hu]
  linarith only [h, h2, h3, h5]

end PseudoPrime.AnalyticNumberTheory.Arithmetic
