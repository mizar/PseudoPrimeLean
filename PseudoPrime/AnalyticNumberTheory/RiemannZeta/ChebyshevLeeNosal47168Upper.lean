/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Certified Lee–Nosal interval endpoint -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- An integer least-common-multiple comparison certifies this bound for `psi 47168`.
The power-of-two comparison is verified by the kernel. -/
theorem psi_47168_upper : Chebyshev.psi 47168 ≤ (47112 : ℝ) := by
  have hc : Nat.lcmUpto 47168 ≤ 2 ^ 67966 := by decide +kernel
  change Chebyshev.psi (↑(47168 : ℕ) : ℝ) ≤ (47112 : ℝ)
  rw [Chebyshev.psi_eq_log_lcmUpto]
  have hp : (0 : ℝ) < (Nat.lcmUpto 47168 : ℝ) := by exact_mod_cast Nat.lcmUpto_pos 47168
  have hc' : (Nat.lcmUpto 47168 : ℝ) ≤ (2 : ℝ) ^ 67966 := by exact_mod_cast hc
  have h := Real.log_le_log hp hc'
  rw [Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  linarith only [h, Real.log_two_lt_d9]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
