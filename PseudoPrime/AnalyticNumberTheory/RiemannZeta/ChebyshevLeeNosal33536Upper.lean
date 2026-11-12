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

/-- A kernel-checked least-common-multiple comparison certifies this bound for `psi 33536`. -/
theorem psi_33536_upper : Chebyshev.psi 33536 ≤ (33551 : ℝ) := by
  have hc : Nat.lcmUpto 33536 ≤ 2 ^ 48401 := by decide +kernel
  change Chebyshev.psi (↑(33536 : ℕ) : ℝ) ≤ (33551 : ℝ)
  rw [Chebyshev.psi_eq_log_lcmUpto]
  have hp : (0 : ℝ) < (Nat.lcmUpto 33536 : ℝ) := by exact_mod_cast Nat.lcmUpto_pos 33536
  have hc' : (Nat.lcmUpto 33536 : ℝ) ≤ (2 : ℝ) ^ 48401 := by exact_mod_cast hc
  have h := Real.log_le_log hp hc'
  rw [Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  linarith only [h, Real.log_two_lt_d9]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
