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

/-- An integer least-common-multiple comparison certifies this bound for `psi 42560`.
The power-of-two comparison is verified by the kernel. -/
theorem psi_42560_upper : Chebyshev.psi 42560 ≤ (42640 : ℝ) := by
  have hc : Nat.lcmUpto 42560 ≤ 2 ^ 61515 := by decide +kernel
  change Chebyshev.psi (↑(42560 : ℕ) : ℝ) ≤ (42640 : ℝ)
  rw [Chebyshev.psi_eq_log_lcmUpto]
  have hp : (0 : ℝ) < (Nat.lcmUpto 42560 : ℝ) := by exact_mod_cast Nat.lcmUpto_pos 42560
  have hc' : (Nat.lcmUpto 42560 : ℝ) ≤ (2 : ℝ) ^ 61515 := by exact_mod_cast hc
  have h := Real.log_le_log hp hc'
  rw [Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  linarith only [h, Real.log_two_lt_d9]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
