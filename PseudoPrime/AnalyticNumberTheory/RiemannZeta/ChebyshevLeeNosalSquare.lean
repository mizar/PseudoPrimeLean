/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-! # Comparing the Lee–Nosal and square-logarithmic envelopes -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Above `exp 1`, the Lee–Nosal error envelope is bounded by the square-logarithmic
envelope with coefficient `1/12`. Positivity of the logarithms and a lower bound for
pi make the comparison independent of any hypothesis about Chebyshev functions. -/
theorem lee_nosal_le_square_twelve {x : ℝ} (hx : Real.exp 1 ≤ x) :
    Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) ≤
      Real.sqrt x * (Real.log x ^ 2 / 12) := by
  have hx0 : 0 < x := (Real.exp_pos 1).trans_le hx
  have hl : 1 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).2 hx
  have hl0 : 0 ≤ Real.log x := zero_le_one.trans hl
  have hll : 0 ≤ Real.log (Real.log x) := Real.log_nonneg hl
  have hp : 0 < 8 * Real.pi := mul_pos (by norm_num only) Real.pi_pos
  have hp12 : (12 : ℝ) ≤ 8 * Real.pi := by linarith only [Real.pi_gt_three]
  have hm := mul_nonneg hl0 hll
  have hn := mul_nonneg (sub_nonneg.mpr hp12) (sq_nonneg (Real.log x))
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg x)
  apply (div_le_div_iff₀ hp (by norm_num only : (0 : ℝ) < 12)).2
  nlinarith only [hm, hn]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
