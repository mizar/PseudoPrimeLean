/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ExplicitUntaperedPrimeRates

/-! # Local even-power cancellation and retained finite exception budgets -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- The weight sum over even positive powers within the root cutoff.
Inputs are a cutoff, arbitrary real weight and natural base; no sign is assumed.
The sum measures the exact mass canceled at a unit square in a quadratic character. -/
noncomputable def evenPrimePowerCost (x : ℝ) (w : ℕ → ℝ) (p : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊,
    if p ≤ ⌊x ^ ((1 : ℝ) / k)⌋₊ ∧ Even k then w (p ^ k) else 0

/-- For a prime coprime to q, its local cost plus twice the even-power mass
equals twice the conductor-zero local cost. Split parity and cutoff cases termwise.
This exact identity needs no positivity and precedes all analytic upper bounds. -/
theorem quadraticPrimeCost_add_even {q p : ℕ} (hp : p.Prime) (hc : Nat.Coprime p q) (x : ℝ)
    (w : ℕ → ℝ) :
    quadraticExcludedPrimeCost q x w p + 2 * evenPrimePowerCost x w p =
      2 * quadraticExcludedPrimeCost 0 x w p := by
  have hc0 : ¬Nat.Coprime p 0 := fun h ↦ hp.ne_one ((Nat.coprime_zero_right p).mp h)
  rw [quadraticExcludedPrimeCost_of_coprime hp hc, quadraticExcludedPrimeCost_of_not_coprime hc0]
  unfold evenPrimePowerCost
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hcut : p ≤ ⌊x ^ ((1 : ℝ) / k)⌋₊ <;> by_cases he : Even k <;>
    simp only [hcut, he, not_true_eq_false, not_false_eq_true, and_true, and_false, ite_true,
      ite_false, mul_zero, zero_add, add_zero]

/-- With nonnegative weights at cutoff powers, the even-power cost is nonnegative.
Sum the nonnegative selected terms; this controls the sign of the cancellation. -/
theorem evenPrimePowerCost_nonneg (p : ℕ) (x : ℝ) (w : ℕ → ℝ)
    (hw : ∀ k ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊, p ≤ ⌊x ^ ((1 : ℝ) / k)⌋₊ → 0 ≤ w (p ^ k)) :
    0 ≤ evenPrimePowerCost x w p := by
  apply Finset.sum_nonneg
  intro k hk
  split_ifs with h
  · exact hw k hk h.1
  · exact le_rfl

end PseudoPrime.AnalyticNumberTheory.Arithmetic
