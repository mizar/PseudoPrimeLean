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

/-- An integer least-common-multiple comparison certifies this bound for `psi 44096`.
The power-of-two comparison is verified by the kernel. -/
theorem psi_44096_upper : Chebyshev.psi 44096 ≤ (44124 : ℝ) := by
  have hc : Nat.lcmUpto 44096 ≤ 2 ^ 63656 := by decide +kernel
  change Chebyshev.psi (↑(44096 : ℕ) : ℝ) ≤ (44124 : ℝ)
  rw [Chebyshev.psi_eq_log_lcmUpto]
  have hp : (0 : ℝ) < (Nat.lcmUpto 44096 : ℝ) := by exact_mod_cast Nat.lcmUpto_pos 44096
  have hc' : (Nat.lcmUpto 44096 : ℝ) ≤ (2 : ℝ) ^ 63656 := by exact_mod_cast hc
  have h := Real.log_le_log hp hc'
  rw [Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  linarith only [h, Real.log_two_lt_d9]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
