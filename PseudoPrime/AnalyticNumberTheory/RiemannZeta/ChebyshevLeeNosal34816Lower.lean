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

/-- A kernel-checked least-common-multiple comparison certifies this bound for `psi 34816`. -/
theorem psi_34816_lower : (34862 : ℝ) ≤ Chebyshev.psi 34816 := by
  have hc : 2 ^ 50298 ≤ Nat.lcmUpto 34816 := by decide +kernel
  change (34862 : ℝ) ≤ Chebyshev.psi (↑(34816 : ℕ) : ℝ)
  rw [Chebyshev.psi_eq_log_lcmUpto]
  have hp : (0 : ℝ) < (2 : ℝ) ^ 50298 := pow_pos (by norm_num only) _
  have hc' : (2 : ℝ) ^ 50298 ≤ (Nat.lcmUpto 34816 : ℝ) := by exact_mod_cast hc
  have h := Real.log_le_log hp hc'
  rw [Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  linarith only [h, Real.log_two_gt_d9]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
