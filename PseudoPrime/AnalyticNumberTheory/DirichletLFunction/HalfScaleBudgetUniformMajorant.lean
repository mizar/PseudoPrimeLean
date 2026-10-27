/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.HalfScaleBudgetCoarseBounds
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.HalfScaleBudgetHeightBounds

/-! # A normalized two-scale majorant for all explicit half-scale remainders -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- Collect the fixed coefficients of the low-height, genus, arithmetic, and
level-change terms after bounding them by a common power-log weight. Only the
remainder and local-count constants vary. The high-tail coefficient remains separate. -/
noncomputable def halfScaleTimeBudgetConstant (C K : ℝ) : ℝ :=
  3 * K * (3 + Real.log 2) * (10 + 5 * Real.log 2) +
    (32 * Real.log 2) * (genusCorrectionBudgetConstant + 1) +
    C +
    1

/-- Nonnegative arithmetic and local-count constants make the common time-budget
constant positive. Each displayed summand is nonnegative and the final one is
positive. This permits uniform positive-error threshold choices. -/
theorem halfScaleTimeBudgetConstant_pos {C K : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K) :
    0 < halfScaleTimeBudgetConstant C K := by
  have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num only)
  have hlow :=
    mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 3) hK)
        (by linarith only [hl] : 0 ≤ 3 + Real.log 2))
      (by linarith only [hl] : 0 ≤ 10 + 5 * Real.log 2)
  have hgen :=
    mul_nonneg (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 32) hl)
      (by linarith only [genusCorrectionBudgetConstant_pos] : 0 ≤ genusCorrectionBudgetConstant + 1)
  dsimp only [halfScaleTimeBudgetConstant]
  linarith only [hlow, hgen, hC]

/-- For modulus at most the square root of `R=H+1`, scale at least four with
`R <= x` and `R^2 <= x^delta`, and the displayed threshold balance, the entire
scalar family remainder is bounded by a height-decaying term and one common
power-log term. Combine the low-height, original-tail, and correction estimates.
All budget constants are nonnegative and no character-dependent expression remains. -/
theorem weighted_primitive_remainder_le_two_scale_majorant {q H : ℕ} {x σ δ C K T : ℝ} (hq : 1 ≤ q)
    (hH : 3 ≤ H) (hqr : q ≤ H + 1) (hsqrt : (q : ℝ) ≤ Real.sqrt ((H + 1 : ℕ) : ℝ)) (hx : 4 ≤ x)
    (hRx : ((H + 1 : ℕ) : ℝ) ≤ x) (hpow : ((H + 1 : ℕ) : ℝ) ^ 2 ≤ x ^ δ) (hσ : 1 / 2 ≤ σ)
    (hbalance : σ + 2 * δ ≤ 1) (hC : 0 ≤ C) (hK : 0 ≤ K) (hT : 0 ≤ T) :
    (q : ℝ) * primitiveHalfScaleRemainderBudget q x σ H C K T + (q : ℝ) ^ 2 * (Real.log x) ^ 2 ≤
      240 * x * T * (Real.log 2 + Real.log ((H + 1 : ℕ) : ℝ) + 2) / Real.sqrt ((H + 1 : ℕ) : ℝ) +
        halfScaleTimeBudgetConstant C K * (x ^ (1 - δ) * (Real.log x + 1) ^ 3) := by
  have hl := weighted_low_height_budget_le_common_weight hq hqr hx hRx hpow hσ hbalance hK
  have ht := weighted_original_high_tail_le hq hH hqr hsqrt (by linarith only [hx] : 0 ≤ x) hT
  have hc :=
    weighted_genus_and_arithmetic_corrections_le_common_weight hq hqr hx hRx hpow hσ hbalance hC
  rw [primitiveHalfScaleRemainderBudget, regularizedHighZeroTailMajorant_eq]
  dsimp only [halfScaleTimeBudgetConstant]
  nlinarith only [hl, ht, hc]

/-- At a positive scale, the common power-log weight equals the scale times
`(log(x)+1)^3/x^delta`. Use real-power subtraction and rearrange. This exposes
the vanishing normalized error used for uniform absorption. -/
theorem rpow_common_weight_eq_scaled_decay {x δ : ℝ} (hx : 0 < x) :
    x ^ (1 - δ) * (Real.log x + 1) ^ 3 = x * ((Real.log x + 1) ^ 3 / x ^ δ) := by
  rw [Real.rpow_sub hx, Real.rpow_one]
  ring

/-- Under the same modulus, height, and exponent-balance hypotheses, divide the
scalar remainder conceptually by its positive scale and bound it by the sum of
two explicit decaying functions, one of height and one of scale. Rewrite the
common weight exactly. This makes both large thresholds independent of the varying family. -/
theorem weighted_primitive_remainder_le_normalized_majorant {q H : ℕ} {x σ δ C K T : ℝ} (hq : 1 ≤ q)
    (hH : 3 ≤ H) (hqr : q ≤ H + 1) (hsqrt : (q : ℝ) ≤ Real.sqrt ((H + 1 : ℕ) : ℝ)) (hx : 4 ≤ x)
    (hRx : ((H + 1 : ℕ) : ℝ) ≤ x) (hpow : ((H + 1 : ℕ) : ℝ) ^ 2 ≤ x ^ δ) (hσ : 1 / 2 ≤ σ)
    (hbalance : σ + 2 * δ ≤ 1) (hC : 0 ≤ C) (hK : 0 ≤ K) (hT : 0 ≤ T) :
    (q : ℝ) * primitiveHalfScaleRemainderBudget q x σ H C K T + (q : ℝ) ^ 2 * (Real.log x) ^ 2 ≤
      x *
        (240 * T * ((Real.log 2 + Real.log ((H + 1 : ℕ) : ℝ) + 2) / Real.sqrt ((H + 1 : ℕ) : ℝ)) +
          halfScaleTimeBudgetConstant C K * ((Real.log x + 1) ^ 3 / x ^ δ)) := by
  have hb :=
    weighted_primitive_remainder_le_two_scale_majorant hq hH hqr hsqrt hx hRx hpow hσ hbalance hC hK
      hT
  rw [rpow_common_weight_eq_scaled_decay (by linarith only [hx] : 0 < x)] at hb
  exact hb.trans_eq (by ring)

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
