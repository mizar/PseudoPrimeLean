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

/-- The kernel-checked least-common-multiple comparison proves a lower bound for `psi 46913`. -/
theorem psi_46913_theta_lower : (46882 : ℝ) ≤ Chebyshev.psi 46913 := by
  have hc : 2 ^ 67639 ≤ Nat.lcmUpto 46913 := by decide +kernel
  change (46882 : ℝ) ≤ Chebyshev.psi (↑(46913 : ℕ) : ℝ)
  rw [Chebyshev.psi_eq_log_lcmUpto]
  have hp : (0 : ℝ) < (2 : ℝ) ^ 67639 := pow_pos (by norm_num only) _
  have hc' : (2 : ℝ) ^ 67639 ≤ (Nat.lcmUpto 46913 : ℝ) := by exact_mod_cast hc
  have h := Real.log_le_log hp hc'
  rw [Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  linarith only [h, Real.log_two_gt_d9]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
