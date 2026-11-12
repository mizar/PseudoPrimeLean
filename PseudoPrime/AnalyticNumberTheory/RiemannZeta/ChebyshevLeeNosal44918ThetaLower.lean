/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Certified psi endpoint for a Lee–Nosal theta interval -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The kernel-checked least-common-multiple comparison proves a lower bound for `psi 44918`. -/
theorem psi_44918_theta_lower : (44961 : ℝ) ≤ Chebyshev.psi 44918 := by
  have hc : 2 ^ 64867 ≤ Nat.lcmUpto 44918 := by decide +kernel
  change (44961 : ℝ) ≤ Chebyshev.psi (↑(44918 : ℕ) : ℝ)
  rw [Chebyshev.psi_eq_log_lcmUpto]
  have hp : (0 : ℝ) < (2 : ℝ) ^ 64867 := pow_pos (by norm_num only) _
  have hc' : (2 : ℝ) ^ 64867 ≤ (Nat.lcmUpto 44918 : ℝ) := by exact_mod_cast hc
  have h := Real.log_le_log hp hc'
  rw [Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  linarith only [h, Real.log_two_gt_d9]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
