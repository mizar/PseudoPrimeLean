/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # A lower endpoint for a finite Lee–Nosal bound -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- A kernel-checked least-common-multiple comparison gives the lower bound for
`psi 40512`. -/
theorem psi_40512_lower : (40479 : ℝ) ≤ Chebyshev.psi 40512 := by
  have hc : 2 ^ 58399 ≤ Nat.lcmUpto 40512 := by decide +kernel
  change (40479 : ℝ) ≤ Chebyshev.psi (↑(40512 : ℕ) : ℝ)
  rw [Chebyshev.psi_eq_log_lcmUpto]
  have hp : (0 : ℝ) < (2 : ℝ) ^ 58399 := pow_pos (by norm_num only) _
  have hc' : (2 : ℝ) ^ 58399 ≤ (Nat.lcmUpto 40512 : ℝ) := by exact_mod_cast hc
  have h := Real.log_le_log hp hc'
  rw [Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  linarith only [h, Real.log_two_gt_d9]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
