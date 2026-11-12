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

/-- A kernel-checked least-common-multiple comparison certifies this bound for `psi 33792`. -/
theorem psi_33792_upper : Chebyshev.psi 33792 ≤ (33853 : ℝ) := by
  have hc : Nat.lcmUpto 33792 ≤ 2 ^ 48837 := by decide +kernel
  change Chebyshev.psi (↑(33792 : ℕ) : ℝ) ≤ (33853 : ℝ)
  rw [Chebyshev.psi_eq_log_lcmUpto]
  have hp : (0 : ℝ) < (Nat.lcmUpto 33792 : ℝ) := by exact_mod_cast Nat.lcmUpto_pos 33792
  have hc' : (Nat.lcmUpto 33792 : ℝ) ≤ (2 : ℝ) ^ 48837 := by exact_mod_cast hc
  have h := Real.log_le_log hp hc'
  rw [Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  linarith only [h, Real.log_two_lt_d9]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
