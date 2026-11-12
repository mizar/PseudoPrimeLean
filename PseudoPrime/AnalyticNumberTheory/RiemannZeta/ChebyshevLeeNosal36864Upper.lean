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

/-- A kernel-checked least-common-multiple comparison certifies this bound for `psi 36864`. -/
theorem psi_36864_upper : Chebyshev.psi 36864 ≤ (36885 : ℝ) := by
  have hc : Nat.lcmUpto 36864 ≤ 2 ^ 53211 := by decide +kernel
  change Chebyshev.psi (↑(36864 : ℕ) : ℝ) ≤ (36885 : ℝ)
  rw [Chebyshev.psi_eq_log_lcmUpto]
  have hp : (0 : ℝ) < (Nat.lcmUpto 36864 : ℝ) := by exact_mod_cast Nat.lcmUpto_pos 36864
  have hc' : (Nat.lcmUpto 36864 : ℝ) ≤ (2 : ℝ) ^ 53211 := by exact_mod_cast hc
  have h := Real.log_le_log hp hc'
  rw [Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  linarith only [h, Real.log_two_lt_d9]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
