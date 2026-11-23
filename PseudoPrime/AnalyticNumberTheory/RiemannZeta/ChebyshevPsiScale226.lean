/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-! # Smoothing-scale conditions above logarithmic height 22.6 -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- For `L ≥ 113/5`, the exponential at `L/2` dominates `100L`.
Split at ten and use elementary exponential lower bounds. -/
theorem exp_half_ge_hundred_mul {L : ℝ} (hL : (113 / 5 : ℝ) ≤ L) : 100 * L ≤ Real.exp (L / 2) := by
  have he10 : (1024 : ℝ) ≤ Real.exp 10 := by
    have h := pow_le_pow_left₀ (show (0 : ℝ) ≤ 2 by norm_num only) Real.exp_one_gt_two.le 10
    rw [← Real.exp_natCast_mul] at h
    norm_num only at h ⊢
    exact h
  have he := Real.add_one_le_exp (L / 2 - 10)
  have hm := mul_le_mul he10 he (by linarith only [hL]) (Real.exp_pos 10).le
  have hexp : Real.exp (L / 2) = Real.exp 10 * Real.exp (L / 2 - 10) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  nlinarith only [hm, hL]

/-- For `L ≥ 113/5`, the relative width `(5L/(6π))/exp(L/2)` is positive,
at most one half, and gives cutoff at least 40. The lower smoothing endpoint
also exceeds one. -/
theorem scale226_conditions {L : ℝ} (hL : (113 / 5 : ℝ) ≤ L) :
    let s := Real.exp (L / 2)
    let q := 5 * L / (6 * Real.pi)
    let δ := q / s
    0 < δ ∧ δ ≤ 1 / 2 ∧ 40 ≤ 2 / δ ∧ 1 < Real.exp L - Real.exp L * δ := by
  dsimp only
  let s := Real.exp (L / 2)
  let q := 5 * L / (6 * Real.pi)
  have he := exp_half_ge_hundred_mul hL
  have hL0 : 0 < L := by linarith only [hL]
  have hs : 0 < s := Real.exp_pos _
  have hp : 0 < 6 * Real.pi := mul_pos (by norm_num only) Real.pi_pos
  have hq : 0 < q := div_pos (mul_pos (by norm_num only) hL0) hp
  have hqL : q ≤ L := by
    dsimp only [q]
    apply (div_le_iff₀ hp).2
    nlinarith only [hL0, Real.pi_gt_three]
  have hs1000 : 1000 ≤ s := by
    change 100 * L ≤ s at he
    nlinarith only [he, hL]
  have hδ : q / s ≤ 1 / 100 := by
    apply (div_le_iff₀ hs).2
    change 100 * L ≤ s at he
    nlinarith only [he, hqL]
  have hδpos : 0 < q / s := div_pos hq hs
  have hcut : 40 ≤ 2 / (q / s) := by
    apply (le_div_iff₀ hδpos).2
    linarith only [hδ]
  have hexp : Real.exp L = s ^ 2 := by
    dsimp only [s]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hp1 := mul_le_mul_of_nonneg_left hδ (sq_nonneg s)
  have hs2 : 0 ≤ s ^ 2 := sq_nonneg s
  have hleft : 1 < Real.exp L - Real.exp L * (q / s) := by
    rw [hexp]
    nlinarith only [hp1, hs2, hs1000]
  exact ⟨hδpos, by linarith only [hδ], hcut, hleft⟩

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
