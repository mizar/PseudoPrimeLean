/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK141TailBudget
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK156TailBudget

/-! # Normalized Euler tail bounds for the middle Gaussian intervals -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The logarithmic cutoffs at or above 20 are in the range of the Abel bound. -/
private theorem middle_tail_exp_large {z : ℝ} (hz : 20 ≤ z) : 101 ≤ Real.exp z := by
  have h := Real.quadratic_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 20)
  exact
    (by norm_num only : (101 : ℝ) ≤ 1 + 20 + 20 ^ 2 / 2).trans (h.trans (Real.exp_le_exp.mpr hz))

/-- The K141 signed Euler tail has normalized cost at most a tenth from
logarithmic cutoff 20 onward, for every deficit function in the interval from zero to four. -/
public theorem middle_k141_tail_normalized (hRH : RiemannHypothesis) {X : ℝ} (hX : 0 < X)
    (hx : 20 ≤ Real.log X) (α : ℕ → ℝ) (hα : ∀ n, α n ∈ Set.Icc 0 4) :
    (middleK141Norm : ℝ) *
        (2 *
          ∑' n : { n : ℕ // ⌊X⌋₊ < n },
            α n.val *
              (ArithmeticFunction.vonMangoldt n.val / Real.sqrt n.val *
                middleMassProfile middleK141Kernel 2 14 n.val)) ≤
      1 / 10 := by
  have ht :=
    middle_k141_tail_from hRH (middle_tail_exp_large le_rfl) (Real.log_exp 20).ge
      ((Real.le_log_iff_exp_le hX).mp hx) α hα
  have hk : (0 : ℝ) ≤ middleK141Norm := Rat.cast_nonneg.mpr (by decide +kernel)
  exact
    (mul_le_mul_of_nonneg_left ht hk).trans
      (by simpa only [mul_assoc, mul_left_comm] using middle_k141_tail_budget)

/-- The K156 signed Euler tail has normalized cost at most one from logarithmic
cutoff 24, and at most one sixtieth from logarithmic cutoff 29. -/
public theorem middle_k156_tail_normalized (hRH : RiemannHypothesis) {X : ℝ} (hX : 0 < X)
    (hx : 24 ≤ Real.log X) (α : ℕ → ℝ) (hα : ∀ n, α n ∈ Set.Icc 0 4) :
    (middleK156Norm : ℝ) *
        (2 *
          ∑' n : { n : ℕ // ⌊X⌋₊ < n },
            α n.val *
              (ArithmeticFunction.vonMangoldt n.val / Real.sqrt n.val *
                middleMassProfile middleK156Kernel (49 / 20) 24 n.val)) ≤
      if 29 ≤ Real.log X then 1 / 60 else 1 := by
  have hk : (0 : ℝ) ≤ middleK156Norm := Rat.cast_nonneg.mpr (by decide +kernel)
  by_cases h : 29 ≤ Real.log X
  · rw [ite_eq_left h]
    have ht :=
      middle_k156_tail_from hRH (middle_tail_exp_large (by norm_num only : (20 : ℝ) ≤ 29))
        ((by norm_num only : (24 : ℝ) ≤ 29).trans (Real.log_exp 29).ge)
        ((Real.le_log_iff_exp_le hX).mp h) α hα
    exact
      (mul_le_mul_of_nonneg_left ht hk).trans
        (by simpa only [mul_assoc, mul_left_comm] using middle_k156_tail_budget_29)
  · rw [ite_eq_right h]
    have ht :=
      middle_k156_tail_from hRH (middle_tail_exp_large (by norm_num only : (20 : ℝ) ≤ 24))
        (Real.log_exp 24).ge ((Real.le_log_iff_exp_le hX).mp hx) α hα
    exact
      (mul_le_mul_of_nonneg_left ht hk).trans
        (by simpa only [mul_assoc, mul_left_comm] using middle_k156_tail_budget_24)

end PseudoPrime.PrimeTestBounds.MillerRabin
