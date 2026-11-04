/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.Tactic.Linarith

/-! # Finite-error logarithmic Stirling bounds

Telescope mathlib's explicit bound for successive logarithmic Stirling differences and pass
to the known limit. The result gives a finite upper error for logarithmic factorials.
-/

@[expose] public section

namespace PseudoPrime.Combinatorics

/-- For positive `x`, the reciprocal product in the Stirling difference estimate is a
telescoping difference. Rewrite the difference of inverses and factor out `1 / 12`.
This is the elementary arithmetic step in the finite Stirling error bound. -/
theorem stirling_reciprocal_step {x : ℝ} (hx : 0 < x) :
    1 / (12 * x * (x + 1)) = 1 / (12 * x) - 1 / (12 * (x + 1)) := by
  have hx0 : x ≠ 0 := hx.ne'
  have hx1 : x + 1 ≠ 0 := (show 0 < x + 1 by linarith only [hx]).ne'
  have h := inv_sub_inv hx0 hx1
  have he : 1 / x - 1 / (x + 1) = 1 / (x * (x + 1)) := by
    simpa only [one_div, add_sub_cancel_left] using h
  calc
    _ = (1 / 12 : ℝ) * (1 / (x * (x + 1))) := by
      simp only [one_div, mul_inv]
      ring
    _ = (1 / 12 : ℝ) * (1 / x - 1 / (x + 1)) := by rw [he]
    _ = _ := by
      simp only [one_div, mul_inv]
      ring

/-- For `n ≥ 1`, the logarithmic Stirling sequence drops by at most the difference
of the reciprocal errors between `n` and `n + k`. Induction telescopes mathlib's
successive-difference estimate. This controls the error before taking the limit. -/
theorem log_stirling_drop_le (n : ℕ) (hn : 1 ≤ n) (k : ℕ) :
    Real.log (Stirling.stirlingSeq n) - Real.log (Stirling.stirlingSeq (n + k)) ≤
      1 / (12 * (n : ℝ)) - 1 / (12 * (n + k : ℕ)) := by
  induction k with
  | zero => simp only [Nat.add_zero, sub_self, le_refl]
  | succ k
    ih =>
    have hp : (0 : ℝ) < (n + k : ℕ) :=
      Nat.cast_pos.mpr (Nat.lt_of_lt_of_le Nat.zero_lt_one (hn.trans (Nat.le_add_right n k)))
    have hs := Stirling.log_stirlingSeq_sdiff_le (n + k)
    rw [stirling_reciprocal_step hp] at hs
    rw [Nat.add_succ, Nat.succ_eq_add_one]
    norm_num only [Nat.cast_add, Nat.cast_one] at hs ih ⊢
    linarith only [ih, hs]

/-- For `n ≥ 1`, the logarithmic Stirling sequence is at most `1 / (12 * n)`
above its limit `log (sqrt pi)`. Bound every finite drop and pass to the known limit.
This provides the explicit remainder for the upper factorial estimate. -/
theorem log_stirling_error_le {n : ℕ} (hn : 1 ≤ n) :
    Real.log (Stirling.stirlingSeq n) - Real.log (Real.sqrt Real.pi) ≤ 1 / (12 * (n : ℝ)) := by
  have hlim :
    Filter.Tendsto (fun k : ℕ ↦ Real.log (Stirling.stirlingSeq (n + k))) Filter.atTop
      (nhds (Real.log (Real.sqrt Real.pi))) := by
    have hlog := Stirling.tendsto_stirlingSeq_sqrt_pi.log (Real.sqrt_pos.mpr Real.pi_pos).ne'
    have h := hlog.comp (Filter.tendsto_add_atTop_nat n)
    convert h using 1
    ext k
    exact congrArg (fun j ↦ Real.log (Stirling.stirlingSeq j)) (Nat.add_comm n k)
  apply le_of_tendsto' (hlim.const_sub _)
  intro k
  have he := log_stirling_drop_le n hn k
  have hpos : 0 ≤ 1 / (12 * ((n + k : ℕ) : ℝ)) :=
    div_nonneg (by norm_num only) (mul_nonneg (by norm_num only) (Nat.cast_nonneg _))
  linarith only [he, hpos]

/-- For every positive natural `n`, `log (n!)` is bounded above by the standard
Stirling main term plus `1 / (12 * n)`. Expand mathlib's logarithmic Stirling sequence
and insert the explicit limit error. This supports sharp finite binomial lower bounds. -/
theorem log_factorial_stirling_le {n : ℕ} (hn : n ≠ 0) :
    Real.log (n.factorial : ℝ) ≤
      n * Real.log n - n + Real.log n / 2 + Real.log (2 * Real.pi) / 2 + 1 / (12 * (n : ℝ)) := by
  have h := log_stirling_error_le (Nat.one_le_iff_ne_zero.mpr hn)
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hp0 : Real.pi ≠ 0 := Real.pi_pos.ne'
  rw [Stirling.log_stirlingSeq_formula, Real.log_div hn0 (Real.exp_ne_zero 1), Real.log_exp,
    Real.log_sqrt Real.pi_pos.le, Real.log_mul (by norm_num only : (2 : ℝ) ≠ 0) hn0] at h
  rw [Real.log_mul (by norm_num only : (2 : ℝ) ≠ 0) hp0]
  linarith only [h]

end PseudoPrime.Combinatorics
