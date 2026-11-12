/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalMonotone

/-! # Derivative of the Lee–Nosal error envelope -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- At every `x > 1`, the Lee–Nosal error envelope has the displayed derivative.
The proof combines the derivatives of the square root, logarithm and iterated logarithm. -/
theorem hasDerivAt_lee_nosal {x : ℝ} (hx : 1 < x) :
    HasDerivAt
      (fun t : ℝ ↦
        Real.sqrt t * (Real.log t * (Real.log t - Real.log (Real.log t)) / (8 * Real.pi)))
      ((Real.log x ^ 2 - Real.log x * Real.log (Real.log x) + 4 * Real.log x -
          2 * Real.log (Real.log x) -
          2) /
        (16 * Real.pi * Real.sqrt x))
      x := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hl0 : 0 < Real.log x := Real.log_pos hx
  have hs0 : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hl := Real.hasDerivAt_log hx0.ne'
  have hll := (Real.hasDerivAt_log hl0.ne').comp x hl
  have hs := Real.hasDerivAt_sqrt hx0.ne'
  have h := hs.mul ((hl.mul (hl.sub hll)).div_const (8 * Real.pi))
  simp only [Pi.mul_apply, Pi.sub_apply, Function.comp_apply] at h
  convert h using 1
  have hsq := Real.sq_sqrt hx0.le
  field_simp [hx0.ne', hl0.ne', hs0.ne', Real.pi_ne_zero]
  rw [hsq]
  ring

/-- If `x ≥ exp 1`, the derivative of the Lee–Nosal envelope is strictly below one.
The proof compares its numerator with a quadratic exponential lower bound. -/
theorem lee_nosal_deriv_lt_one {x : ℝ} (hx : Real.exp 1 ≤ x) :
    (Real.log x ^ 2 - Real.log x * Real.log (Real.log x) + 4 * Real.log x -
          2 * Real.log (Real.log x) -
          2) /
        (16 * Real.pi * Real.sqrt x) <
      1 := by
  have hx0 : 0 < x := (Real.exp_pos 1).trans_le hx
  have hl : 1 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).2 hx
  have hlog0 : 0 ≤ Real.log x := (show (0 : ℝ) ≤ 1 by norm_num only).trans hl
  have hll0 : 0 ≤ Real.log (Real.log x) := Real.log_nonneg hl
  have hmul := mul_nonneg hlog0 hll0
  have ht : 0 ≤ Real.log x / 2 := div_nonneg hlog0 (by norm_num only)
  have hquad := Real.quadratic_le_exp_of_nonneg ht
  have hexp : Real.exp (Real.log x / 2) = Real.sqrt x := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx0]
    congr 1
    ring
  rw [hexp] at hquad
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hpi := mul_pos (show 0 < Real.pi - 3 by linarith only [Real.pi_gt_three]) hs
  apply (div_lt_one (by nlinarith only [Real.pi_pos, hs] : 0 < 16 * Real.pi * Real.sqrt x)).2
  nlinarith only [hquad, hmul, hll0, hlog0, hpi, sq_nonneg (Real.log x)]

/-- The function `x - B(x)`, where `B` is the Lee–Nosal envelope, is nondecreasing
on `[exp 1, ∞)`. Its derivative is nonnegative because the envelope derivative is below one. -/
theorem lee_nosal_sub_mono :
    MonotoneOn
      (fun t : ℝ ↦
        t - Real.sqrt t * (Real.log t * (Real.log t - Real.log (Real.log t)) / (8 * Real.pi)))
      (Set.Ici (Real.exp 1)) := by
  have hexp : (1 : ℝ) < Real.exp 1 := by
    have h := Real.add_one_le_exp 1
    linarith only [h]
  have hderiv (t : ℝ) (ht : Real.exp 1 ≤ t) :=
    (hasDerivAt_id t).sub (hasDerivAt_lee_nosal (hexp.trans_le ht))
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici (Real.exp 1))
  · intro t ht
    exact (hderiv t ht).continuousAt.continuousWithinAt
  · intro t ht
    exact (hderiv t (interior_subset ht)).hasDerivWithinAt
  · intro t ht
    exact sub_nonneg.mpr (lee_nosal_deriv_lt_one (interior_subset ht)).le

/-- The function `x + B(x)`, where `B` is the Lee–Nosal envelope, is nondecreasing
on `[exp 1, ∞)` because the envelope itself is nondecreasing there. -/
theorem lee_nosal_add_mono :
    MonotoneOn
      (fun t : ℝ ↦
        t + Real.sqrt t * (Real.log t * (Real.log t - Real.log (Real.log t)) / (8 * Real.pi)))
      (Set.Ici (Real.exp 1)) := by
  intro x hx y _ hxy
  have h := lee_nosal_envelope_mono hx hxy
  linarith only [h, hxy]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
