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

/-- An integer least-common-multiple comparison certifies this bound for `psi 45632`.
The power-of-two comparison is verified by the kernel. -/
theorem psi_45632_upper : Chebyshev.psi 45632 ≤ (45629 : ℝ) := by
  have hc : Nat.lcmUpto 45632 ≤ 2 ^ 65827 := by decide +kernel
  change Chebyshev.psi (↑(45632 : ℕ) : ℝ) ≤ (45629 : ℝ)
  rw [Chebyshev.psi_eq_log_lcmUpto]
  have hp : (0 : ℝ) < (Nat.lcmUpto 45632 : ℝ) := by exact_mod_cast Nat.lcmUpto_pos 45632
  have hc' : (Nat.lcmUpto 45632 : ℝ) ≤ (2 : ℝ) ^ 65827 := by exact_mod_cast hc
  have h := Real.log_le_log hp hc'
  rw [Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  linarith only [h, Real.log_two_lt_d9]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
