/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # A certified endpoint for the Lee–Nosal interval -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The Chebyshev value at 40512 is at most 40481. The kernel checks the
least-common-multiple comparison, and a rational logarithm bound closes the estimate. -/
theorem psi_40512_upper : Chebyshev.psi 40512 ≤ (40481 : ℝ) := by
  have hc : Nat.lcmUpto 40512 ≤ 2 ^ 58400 := by decide +kernel
  change Chebyshev.psi (↑(40512 : ℕ) : ℝ) ≤ (40481 : ℝ)
  rw [Chebyshev.psi_eq_log_lcmUpto]
  have hp : (0 : ℝ) < (Nat.lcmUpto 40512 : ℝ) := by exact_mod_cast Nat.lcmUpto_pos 40512
  have hc' : (Nat.lcmUpto 40512 : ℝ) ≤ (2 : ℝ) ^ 58400 := by exact_mod_cast hc
  have h := Real.log_le_log hp hc'
  rw [Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  linarith only [h, Real.log_two_lt_d9]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
