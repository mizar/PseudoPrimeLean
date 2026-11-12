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

/-- An integer least-common-multiple comparison certifies this bound for `psi 46144`.
The power-of-two comparison is verified by the kernel. -/
theorem psi_46144_lower : (46098 : ℝ) ≤ Chebyshev.psi 46144 := by
  have hc : 2 ^ 66507 ≤ Nat.lcmUpto 46144 := by decide +kernel
  change (46098 : ℝ) ≤ Chebyshev.psi (↑(46144 : ℕ) : ℝ)
  rw [Chebyshev.psi_eq_log_lcmUpto]
  have hp : (0 : ℝ) < (2 : ℝ) ^ 66507 := pow_pos (by norm_num only) _
  have hc' : (2 : ℝ) ^ 66507 ≤ (Nat.lcmUpto 46144 : ℝ) := by exact_mod_cast hc
  have h := Real.log_le_log hp hc'
  rw [Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  linarith only [h, Real.log_two_gt_d9]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
