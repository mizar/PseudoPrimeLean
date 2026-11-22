/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.Real.Sqrt
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.Scan

/-! # Real interpretation of fixed-point crossing checks -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

/-- A successful integer comparison bounds the scaled error by the real
square-root envelope. Taking square roots preserves the comparison because
the scale, error, numerator and denominator are nonnegative. -/
theorem within_sound {e x u v : ℕ} (h : within e x u v = true) :
    (v : ℝ) * e ≤ Real.sqrt x * ((scale : ℝ) * u) := by
  have hn : (v * e) ^ 2 ≤ x * (scale * u) ^ 2 := of_decide_eq_true h
  have hr : ((v : ℝ) * e) ^ 2 ≤ (x : ℝ) * ((scale : ℝ) * u) ^ 2 := by exact_mod_cast hn
  simpa only [Real.sqrt_sq (mul_nonneg (Nat.cast_nonneg v) (Nat.cast_nonneg e)),
    Real.sqrt_mul (Nat.cast_nonneg x),
    Real.sqrt_sq (mul_nonneg (Nat.cast_nonneg scale) (Nat.cast_nonneg u))] using
    Real.sqrt_le_sqrt hr

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
