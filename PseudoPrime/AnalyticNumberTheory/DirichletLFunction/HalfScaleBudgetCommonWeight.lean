/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.HalfScaleBudgetPowerBounds

/-! # A common power-log weight for half-scale remainder terms -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- At scale at least two, the cube of `log(x)+1` dominates both that logarithm
plus one and its original logarithm squared. Use nonnegativity of `log x`.
This supplies one common logarithmic weight for all remainder terms. -/
theorem log_add_one_le_cube {x : ℝ} (hx : 2 ≤ x) :
    Real.log x + 1 ≤ (Real.log x + 1) ^ 3 ∧ (Real.log x) ^ 2 ≤ (Real.log x + 1) ^ 3 := by
  let L := Real.log x + 1
  have hl : 0 ≤ Real.log x := Real.log_nonneg (by linarith only [hx])
  have hL : 1 ≤ L := by
    dsimp only [L]; linarith only [hl]
  have hLsq : 1 ≤ L ^ 2 := by nlinarith only [hL, sq_nonneg (L - 1)]
  have hmul := mul_nonneg (sq_nonneg L) (sub_nonneg.mpr hL)
  have hmul' := mul_le_mul_of_nonneg_right hLsq (by linarith only [hL] : 0 ≤ L)
  have hlsq : (Real.log x) ^ 2 ≤ L ^ 2 := by
    dsimp only [L]
    nlinarith only [hl]
  change L ≤ L ^ 3 ∧ (Real.log x) ^ 2 ≤ L ^ 3
  constructor <;> nlinarith only [hmul, hmul', hlsq]

/-- At scale at least two and threshold at least one half, the condition
`sigma + 2 delta <= 1` bounds the linear and quadratic logarithmic terms weighted
by `x^delta` by `x^(1-delta)(log(x)+1)^3`. Compare powers and logarithmic factors
separately. This absorbs the origin and level-change corrections into one weight. -/
theorem rpow_log_terms_le_common_weight {x σ δ : ℝ} (hx : 2 ≤ x) (hσ : 1 / 2 ≤ σ)
    (hbalance : σ + 2 * δ ≤ 1) :
    x ^ δ * (Real.log x + 1) ≤ x ^ (1 - δ) * (Real.log x + 1) ^ 3 ∧
      x ^ δ * (Real.log x) ^ 2 ≤ x ^ (1 - δ) * (Real.log x + 1) ^ 3 := by
  have hp :=
    Real.rpow_le_rpow_of_exponent_le (by linarith only [hx] : 1 ≤ x)
      (by linarith only [hσ, hbalance] : δ ≤ 1 - δ)
  have hl := log_add_one_le_cube hx
  have hr := Real.rpow_nonneg (by linarith only [hx] : 0 ≤ x) (1 - δ)
  have hlog : 0 ≤ Real.log x + 1 := by
    have h := Real.log_nonneg (by linarith only [hx] : 1 ≤ x)
    linarith only [h]
  exact ⟨mul_le_mul hp hl.1 hlog hr, mul_le_mul hp hl.2 (sq_nonneg _) hr⟩

/-- Under the same scale, threshold, and exponent-balance conditions, multiply
the combined low-height majorant by `x^delta(log(x)+1)` and bound it by the common
power-log weight times `10+5 log 2`. Combine the low-height power bound with real
power addition and exponent monotonicity. This controls the total low-height family cost. -/
theorem rpow_log_low_majorant_le_common_weight {x σ δ : ℝ} (hx : 2 ≤ x) (hσ : 1 / 2 ≤ σ)
    (hbalance : σ + 2 * δ ≤ 1) :
    x ^ δ * (Real.log x + 1) * regularizedLowHeightMajorant x σ ≤
      (10 + 5 * Real.log 2) * (x ^ (1 - δ) * (Real.log x + 1) ^ 3) := by
  have hxpos : 0 < x := by linarith only [hx]
  have hlog : 0 ≤ Real.log x + 1 := by
    have h := Real.log_nonneg (by linarith only [hx] : 1 ≤ x)
    linarith only [h]
  have hc : 0 ≤ 10 + 5 * Real.log 2 := by
    linarith only [Real.log_nonneg (by norm_num only : (1 : ℝ) ≤ 2)]
  have hm :=
    mul_le_mul_of_nonneg_left (regularizedLowHeightMajorant_le_power_log_square hx hσ)
      (mul_nonneg (Real.rpow_nonneg hxpos.le δ) hlog)
  have hp :=
    Real.rpow_le_rpow_of_exponent_le (by linarith only [hx] : 1 ≤ x)
      (by linarith only [hbalance] : δ + σ ≤ 1 - δ)
  calc
    _ ≤ x ^ δ * (Real.log x + 1) * ((10 + 5 * Real.log 2) * x ^ σ * (Real.log x + 1) ^ 2) := hm
    _ = (10 + 5 * Real.log 2) * x ^ (δ + σ) * (Real.log x + 1) ^ 3 := by
      rw [Real.rpow_add hxpos]
      ring
    _ ≤ _ := by
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hc) (pow_nonneg hlog 3)

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
