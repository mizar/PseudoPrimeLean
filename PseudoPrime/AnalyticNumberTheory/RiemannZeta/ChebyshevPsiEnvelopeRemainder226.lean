/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! # Uniform remainder for the high-range Chebyshev envelope -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Differentiate a positive integer power times `exp(-t/2)`; this controls
the polynomial-exponential factors in the envelope remainder. -/
private theorem pow_exp_neg_half_deriv (n : ℕ) {t : ℝ} :
    HasDerivAt (fun x : ℝ ↦ x ^ (n + 1) * Real.exp (-x / 2))
      (t ^ n * ((n + 1 : ℕ) - t / 2) * Real.exp (-t / 2)) t := by
  have hpow := (hasDerivAt_id t).pow (n + 1)
  have harg := ((hasDerivAt_id t).neg).div_const 2
  have hexp := (Real.hasDerivAt_exp (-t / 2)).comp t harg
  have h := hpow.mul hexp
  convert h using 1
  · funext x
    simp only [Pi.mul_apply, Pi.pow_apply, Pi.neg_apply, Function.comp_apply, id_eq]
  · simp only [Pi.pow_apply, Pi.neg_apply, Function.comp_apply, id_eq, Nat.add_sub_cancel,
      Nat.cast_add, Nat.cast_one, mul_one]
    rw [pow_succ]
    ring

/-- For `n ≤ 2`, the function `t^(n+1) * exp(-t/2)` decreases on
`[113/5, ∞)`. Its derivative is nonpositive there. -/
private theorem pow_exp_neg_half_antitone (n : ℕ) (hn : n ≤ 2) :
    AntitoneOn (fun x : ℝ ↦ x ^ (n + 1) * Real.exp (-x / 2)) (Set.Ici (113 / 5 : ℝ)) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici _)
  · intro t ht
    exact (pow_exp_neg_half_deriv n).continuousAt.continuousWithinAt
  · intro t ht
    exact (pow_exp_neg_half_deriv n).differentiableAt.differentiableWithinAt
  · intro t ht
    have ht' : (113 / 5 : ℝ) ≤ t := interior_subset ht
    have hn' : (n : ℝ) ≤ 2 := by exact_mod_cast hn
    rw [(pow_exp_neg_half_deriv n).deriv]
    have hpow : 0 ≤ t ^ n := pow_nonneg (by linarith only [ht']) _
    have hneg : ((n + 1 : ℕ) : ℝ) - t / 2 ≤ 0 := by
      norm_num only [Nat.cast_add, Nat.cast_one]
      linarith only [ht', hn']
    exact
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hpow hneg) (Real.exp_pos _).le

/-- The exponential at `113/10` is at least 80000. A finite positive Taylor
sum supplies the lower bound using exact arithmetic. -/
private theorem exp_113_tenths_ge : (80000 : ℝ) ≤ Real.exp (113 / 10) := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 113 / 10) 25
  have hc : (80000 : ℝ) ≤ ∑ k ∈ Finset.range 25, (113 / 10 : ℝ) ^ k / k.factorial := by
    norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  exact hc.trans h

/-- For `L ≥ 113/5`, the polynomial-exponential expression bounding the
envelope remainder is at most `21/10000`. Each term decreases from the
endpoint, where an exact exponential lower bound supplies the estimate. -/
theorem envelope226_remainder_bound {L : ℝ} (hL : (113 / 5 : ℝ) ≤ L) :
    Real.exp (-L / 2) * (5 * L ^ 3 / 432 + 5 * L ^ 2 / 108 + 11 * L / 54 + 2) + Real.exp (-L) / 5 ≤
      21 / 10000 := by
  let L0 : ℝ := 113 / 5
  have h0 : Real.exp (-L / 2) ≤ Real.exp (-L0 / 2) := by
    apply Real.exp_le_exp.mpr
    dsimp only [L0] at *
    linarith only [hL]
  have h1 :=
    (pow_exp_neg_half_antitone 0 (by norm_num only)) (show L0 ∈ Set.Ici L0 from le_rfl) hL hL
  have h2 :=
    (pow_exp_neg_half_antitone 1 (by norm_num only)) (show L0 ∈ Set.Ici L0 from le_rfl) hL hL
  have h3 :=
    (pow_exp_neg_half_antitone 2 (by norm_num only)) (show L0 ∈ Set.Ici L0 from le_rfl) hL hL
  norm_num only [Nat.reduceAdd, pow_one] at h1 h2 h3
  have he0 : Real.exp (-L0 / 2) ≤ (1 / 80000 : ℝ) := by
    have he : Real.exp (-L0 / 2) = (Real.exp (113 / 10))⁻¹ := by
      dsimp only [L0]
      rw [show (-(113 / 5 : ℝ) / 2) = -(113 / 10) by ring, Real.exp_neg]
    rw [he, one_div]
    exact (inv_le_inv₀ (Real.exp_pos _) (by norm_num only : (0 : ℝ) < 80000)).2 exp_113_tenths_ge
  have hp : 0 ≤ Real.exp (-L / 2) := (Real.exp_pos _).le
  have heL : Real.exp (-L) = Real.exp (-L / 2) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hsmall : Real.exp (-L / 2) ≤ (1 / 80000 : ℝ) := h0.trans he0
  have hsq := mul_le_mul hsmall hsmall hp (by norm_num only : (0 : ℝ) ≤ 1 / 80000)
  rw [heL]
  dsimp only [L0] at h0 h1 h2 h3 he0
  nlinarith only [h0, h1, h2, h3, he0, hsq]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
