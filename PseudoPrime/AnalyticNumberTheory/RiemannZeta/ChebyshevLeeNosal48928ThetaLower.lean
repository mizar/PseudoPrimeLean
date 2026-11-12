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

/-- The kernel-checked least-common-multiple comparison proves a lower bound for `psi 48928`. -/
theorem psi_48928_theta_lower : (48865 : ℝ) ≤ Chebyshev.psi 48928 := by
  have hc : 2 ^ 70500 ≤ Nat.lcmUpto 48928 := by decide +kernel
  change (48865 : ℝ) ≤ Chebyshev.psi (↑(48928 : ℕ) : ℝ)
  rw [Chebyshev.psi_eq_log_lcmUpto]
  have hp : (0 : ℝ) < (2 : ℝ) ^ 70500 := pow_pos (by norm_num only) _
  have hc' : (2 : ℝ) ^ 70500 ≤ (Nat.lcmUpto 48928 : ℝ) := by exact_mod_cast hc
  have h := Real.log_le_log hp hc'
  rw [Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  linarith only [h, Real.log_two_gt_d9]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
