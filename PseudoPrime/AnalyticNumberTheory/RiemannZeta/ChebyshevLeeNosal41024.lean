/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # An upper endpoint for a finite Lee–Nosal bound -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- A kernel-checked least-common-multiple comparison gives the upper bound for
`psi 41024`. -/
theorem psi_41024_upper : Chebyshev.psi 41024 ≤ (40979 : ℝ) := by
  have hc : Nat.lcmUpto 41024 ≤ 2 ^ 59120 := by decide +kernel
  change Chebyshev.psi (↑(41024 : ℕ) : ℝ) ≤ (40979 : ℝ)
  rw [Chebyshev.psi_eq_log_lcmUpto]
  have hp : (0 : ℝ) < (Nat.lcmUpto 41024 : ℝ) := by exact_mod_cast Nat.lcmUpto_pos 41024
  have hc' : (Nat.lcmUpto 41024 : ℝ) ≤ (2 : ℝ) ^ 59120 := by exact_mod_cast hc
  have h := Real.log_le_log hp hc'
  rw [Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  linarith only [h, Real.log_two_lt_d9]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
