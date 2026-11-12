/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Certified psi endpoint for finite Lee–Nosal intervals -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- A kernel-checked least-common-multiple comparison certifies this bound for `psi 38144`. -/
theorem psi_38144_upper : Chebyshev.psi 38144 ≤ (38122 : ℝ) := by
  have hc : Nat.lcmUpto 38144 ≤ 2 ^ 54996 := by decide +kernel
  change Chebyshev.psi (↑(38144 : ℕ) : ℝ) ≤ (38122 : ℝ)
  rw [Chebyshev.psi_eq_log_lcmUpto]
  have hp : (0 : ℝ) < (Nat.lcmUpto 38144 : ℝ) := by exact_mod_cast Nat.lcmUpto_pos 38144
  have hc' : (Nat.lcmUpto 38144 : ℝ) ≤ (2 : ℝ) ^ 54996 := by exact_mod_cast hc
  have h := Real.log_le_log hp hc'
  rw [Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  linarith only [h, Real.log_two_lt_d9]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
