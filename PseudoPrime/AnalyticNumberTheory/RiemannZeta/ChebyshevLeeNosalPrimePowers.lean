/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevLinearBound
import PseudoPrime.AnalyticNumberTheory.Arithmetic.CompositeMangoldtSqrtBound

/-! # Prime-power mass for the finite Lee–Nosal interval -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- For `0 ≤ x ≤ 50000`, the nonprime-power mass is at most 300. The proof retains
the square, cube and fifth roots in the global linear psi bound. -/
theorem psi_sub_theta_le_300 {x : ℝ} (hx : 0 ≤ x) (hmax : x ≤ 50000) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 300 := by
  have h :=
    Arithmetic.psi_sub_theta_le_roots (C := (111 / 100 : ℝ)) hx
      (fun t ht ↦ Arithmetic.psi_le_111 ht)
  have h2 : Real.sqrt x ≤ 224 := by
    have hs := Real.sqrt_le_sqrt (show x ≤ (224 : ℝ) ^ 2 by nlinarith only [hmax])
    rw [Real.sqrt_sq (by norm_num only)] at hs
    exact hs
  have h3 : x ^ (1 / 3 : ℝ) ≤ 37 := by
    rw [one_div]
    apply
      (Real.rpow_inv_le_iff_of_pos hx (by norm_num only : (0 : ℝ) ≤ 37)
          (by norm_num only : (0 : ℝ) < 3)).2
    norm_num only [Real.rpow_ofNat]
    linarith only [hmax]
  have h5 : x ^ (1 / 5 : ℝ) ≤ 9 := by
    rw [one_div]
    apply
      (Real.rpow_inv_le_iff_of_pos hx (by norm_num only : (0 : ℝ) ≤ 9)
          (by norm_num only : (0 : ℝ) < 5)).2
    norm_num only [Real.rpow_ofNat]
    linarith only [hmax]
  linarith only [h, h2, h3, h5]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
