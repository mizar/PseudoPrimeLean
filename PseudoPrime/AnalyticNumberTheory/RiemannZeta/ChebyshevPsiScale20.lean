/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Calculus.Deriv.Pow

/-! # Smoothing-scale conditions above logarithmic height 20 -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The exponential at ten is at least 22000. An exact finite Taylor sum
provides the lower bound used by the middle-range smoothing scale. -/
theorem exp_ten_ge_22000 : (22000 : ℝ) ≤ Real.exp 10 := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 10) 25
  have hc : (22000 : ℝ) ≤ ∑ k ∈ Finset.range 25, (10 : ℝ) ^ k / k.factorial := by
    norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  exact hc.trans h

/-- For `L ≥ 20`, the exponential at `L/2` dominates `100L`. Split the
exponential at ten and use its tangent-line lower bound. -/
theorem exp_half_ge_hundred_of_twenty {L : ℝ} (hL : 20 ≤ L) : 100 * L ≤ Real.exp (L / 2) := by
  have he := Real.add_one_le_exp (L / 2 - 10)
  have hm := mul_le_mul exp_ten_ge_22000 he (by linarith only [hL]) (Real.exp_pos 10).le
  have hexp : Real.exp (L / 2) = Real.exp 10 * Real.exp (L / 2 - 10) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  nlinarith only [hm, hL]

/-- For `L ≥ 20`, the relative smoothing width `(L/4)/exp(L/2)` is positive,
at most one half, and yields cutoff at least 100. The lower averaging
endpoint is greater than one. -/
theorem scale20_conditions {L : ℝ} (hL : 20 ≤ L) :
    let s := Real.exp (L / 2)
    let δ := (L / 4) / s
    0 < δ ∧ δ ≤ 1 / 2 ∧ 100 ≤ 2 / δ ∧ 1 < Real.exp L - Real.exp L * δ := by
  dsimp only
  let s := Real.exp (L / 2)
  let q := L / 4
  have he := exp_half_ge_hundred_of_twenty hL
  have hL0 : 0 < L := by linarith only [hL]
  have hs : 0 < s := Real.exp_pos _
  have hq : 0 < q := by
    dsimp only [q]; linarith only [hL]
  have hs1000 : 1000 ≤ s := by
    change 100 * L ≤ s at he
    nlinarith only [he, hL]
  have hδ : q / s ≤ 1 / 100 := by
    apply (div_le_iff₀ hs).2
    change 100 * L ≤ s at he
    dsimp only [q]
    nlinarith only [he, hL]
  have hδpos : 0 < q / s := div_pos hq hs
  have hcut : 100 ≤ 2 / (q / s) := by
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
