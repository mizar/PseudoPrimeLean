/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevIntervalPrefix

/-! # Fixed-point steps for Chebyshev psi -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- Fixed-point lower and upper bounds for `psi n` and the next Mangoldt
increment give bounds for `psi(n+1)`. This combines independently certified
increments without exposing any numerical table. -/
theorem psi_fixed_step (n S lo hi wlo whi : ℕ) (hlo : (lo : ℝ) ≤ S * Chebyshev.psi n)
    (hhi : (S : ℝ) * Chebyshev.psi n ≤ hi)
    (hwlo : (wlo : ℝ) ≤ S * ArithmeticFunction.vonMangoldt (n + 1))
    (hwhi : (S : ℝ) * ArithmeticFunction.vonMangoldt (n + 1) ≤ whi) :
    ((lo + wlo : ℕ) : ℝ) ≤ S * Chebyshev.psi (n + 1 : ℕ) ∧
      (S : ℝ) * Chebyshev.psi (n + 1 : ℕ) ≤ ((hi + whi : ℕ) : ℝ) := by
  have h := psi_prefix_add_interval (a := n) (b := n + 1) (Nat.le_succ n)
  rw [Nat.Ioc_succ_singleton, Finset.sum_singleton] at h
  have hm := congrArg (fun t : ℝ ↦ (S : ℝ) * t) h
  simp only [Nat.cast_add, Nat.cast_one] at hm ⊢
  constructor
  · nlinarith only [hlo, hwlo, hm]
  · nlinarith only [hhi, hwhi, hm]

end PseudoPrime.AnalyticNumberTheory.Arithmetic
