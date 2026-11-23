/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # From a square-root psi error to the Lee–Nosal envelope -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- If `log x ≥ 6`, a four-fifths square-root psi error implies the
Lee–Nosal error bound at `x`. A logarithmic tangent bound and the explicit
upper bound for `π` compare the two coefficients. -/
theorem psi_lee_nosal_of_four_fifths {x : ℝ} (hL : 6 ≤ Real.log x)
    (hψ : |Chebyshev.psi x - x| ≤ (4 / 5 : ℝ) * Real.sqrt x) :
    |Chebyshev.psi x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  have hL0 : 0 < Real.log x := by linarith only [hL]
  have hl := Real.log_le_sub_one_of_pos (show 0 < Real.log x / 3 by linarith only [hL])
  rw [Real.log_div hL0.ne' (by norm_num only : (3 : ℝ) ≠ 0)] at hl
  have hlog : Real.log (Real.log x) ≤ Real.log x / 3 + 1 / 2 := by
    linarith only [hl, Real.log_three_lt_d9]
  have hm := mul_le_mul_of_nonneg_left hlog hL0.le
  have hs := sq_nonneg (Real.log x - 6)
  have hp : Real.pi < (22 / 7 : ℝ) := by linarith only [Real.pi_lt_d4]
  have hc : (4 / 5 : ℝ) ≤ Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi) := by
    apply (le_div_iff₀ (mul_pos (by norm_num only) Real.pi_pos)).2
    nlinarith only [hm, hs, hL, hp]
  apply hψ.trans
  simpa only [mul_comm] using (mul_le_mul_of_nonneg_left hc (Real.sqrt_nonneg x))

/-- A real number at least `1423` has logarithm at least six. The elementary
bound `exp 6 ≤ 3⁶ = 729` supplies the comparison needed by the conversion. -/
theorem six_le_log_of_1423_le {x : ℝ} (hx : 1423 ≤ x) : 6 ≤ Real.log x := by
  have he : Real.exp 6 ≤ (729 : ℝ) := by
    have h := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le 6
    rw [← Real.exp_nat_mul] at h
    norm_num only at h ⊢
    exact h
  have h := Real.log_le_log (Real.exp_pos 6) (he.trans (by linarith only [hx]))
  simpa only [Real.log_exp] using h

/-- Above `1423`, the four-fifths square-root psi error implies the
Lee–Nosal envelope. This transfers any certified finite interval directly. -/
theorem psi_lee_nosal_of_1423 {x : ℝ} (hx : 1423 ≤ x)
    (hψ : |Chebyshev.psi x - x| ≤ (4 / 5 : ℝ) * Real.sqrt x) :
    |Chebyshev.psi x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  exact psi_lee_nosal_of_four_fifths (six_le_log_of_1423_le hx) hψ

end PseudoPrime.AnalyticNumberTheory.Arithmetic
