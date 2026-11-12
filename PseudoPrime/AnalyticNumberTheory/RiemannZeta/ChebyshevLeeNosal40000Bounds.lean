/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevLcmBounds

/-! # A kernel-certified Chebyshev checkpoint at 40000 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The Chebyshev value at 40000 lies in `[40012, 40014]`. Integer comparisons bracket
its least common multiple by powers of two, and certified bounds for `log 2` give the interval. -/
theorem psi_40000_bounds : (40012 : ℝ) ≤ Chebyshev.psi 40000 ∧ Chebyshev.psi 40000 ≤ 40014 := by
  have hlower : 2 ^ 57726 ≤ Nat.lcmUpto 40000 := by decide +kernel
  have hupper : Nat.lcmUpto 40000 ≤ 2 ^ (57726 + 1) := by decide +kernel
  have h := Arithmetic.psi_bounds_of_lcm_pow_two hlower hupper
  norm_num only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] at h
  constructor <;> linarith only [h.1, h.2, Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The absolute Chebyshev error at 40000 is at most 14. This follows from the
kernel-certified two-sided interval for `psi 40000`. -/
theorem psi_error_40000_le_fourteen : |Chebyshev.psi 40000 - 40000| ≤ (14 : ℝ) := by
  apply abs_le.mpr
  constructor <;> linarith only [psi_40000_bounds.1, psi_40000_bounds.2]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
