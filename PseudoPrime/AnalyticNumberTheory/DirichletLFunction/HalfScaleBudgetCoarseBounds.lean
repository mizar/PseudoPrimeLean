/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.HalfScaleBudgetCommonWeight

/-! # Coarse common-weight bounds for time-dependent half-scale remainders -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- At scale at least four, let the positive modulus be bounded by `R=H+1`,
with `R <= x` and `R^2 <= x^delta`. A threshold at least one half and exponent
balance `sigma + 2 delta <= 1` put the level-weighted low-height budget below the
common power-log weight times the displayed constant. Compare counting and
logarithmic coefficients before applying the low-height common-weight lemma.
This estimate is uniform in modulus and height. -/
theorem weighted_low_height_budget_le_common_weight {q H : ℕ} {x σ δ K : ℝ} (hq : 1 ≤ q)
    (hqr : q ≤ H + 1) (hx : 4 ≤ x) (hRx : ((H + 1 : ℕ) : ℝ) ≤ x)
    (hpow : ((H + 1 : ℕ) : ℝ) ^ 2 ≤ x ^ δ) (hσ : 1 / 2 ≤ σ) (hbalance : σ + 2 * δ ≤ 1)
    (hK : 0 ≤ K) :
    (q : ℝ) *
        ((2 * ((H + 1 : ℕ) : ℝ) + 1) * K * (Real.log q + Real.log (4 + ((H + 1 : ℕ) : ℝ)) + 1)) *
        regularizedLowHeightMajorant x σ ≤
      (3 * K * (3 + Real.log 2) * (10 + 5 * Real.log 2)) *
        (x ^ (1 - δ) * (Real.log x + 1) ^ 3) := by
  let R : ℝ := ((H + 1 : ℕ) : ℝ)
  have hR : 1 ≤ R := by
    dsimp only [R]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le H)
  have hx2 : 2 ≤ x := by linarith only [hx]
  have hxpos : 0 < x := by linarith only [hx]
  have hqR : (q : ℝ) ≤ R := Nat.cast_le.mpr hqr
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg (by linarith only [hx])
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num only)
  have hlogq0 : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  have hlogh0 : 0 ≤ Real.log (4 + R) := Real.log_nonneg (by linarith only [hR])
  have hlogq :=
    Real.log_le_log (by exact_mod_cast Nat.zero_lt_of_lt hq : (0 : ℝ) < q) (hqR.trans hRx)
  have hlogh :=
    Real.log_le_log (by linarith only [hR] : 0 < 4 + R) (by linarith only [hx, hRx] : 4 + R ≤ 2 * x)
  rw [Real.log_mul (by norm_num only : (2 : ℝ) ≠ 0) hxpos.ne'] at hlogh
  have hlogbound : Real.log q + Real.log (4 + R) + 1 ≤ (3 + Real.log 2) * (Real.log x + 1) := by
    nlinarith only [hlogq, hlogh, mul_nonneg (by linarith only [hlog2] : 0 ≤ 1 + Real.log 2) hlogx]
  have hp :=
    mul_le_mul hqR (by linarith only [hR] : 2 * R + 1 ≤ 3 * R)
      (by linarith only [hR] : 0 ≤ 2 * R + 1) (by linarith only [hR] : 0 ≤ R)
  have hpK := mul_le_mul_of_nonneg_right hp hK
  have hpR := mul_le_mul_of_nonneg_left hpow (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 3) hK)
  have hcoeff : (q : ℝ) * (2 * R + 1) * K ≤ 3 * K * x ^ δ := by nlinarith only [hpK, hpR]
  have hlarge : 0 ≤ 3 * K * x ^ δ :=
    mul_nonneg (mul_nonneg (by norm_num only) hK) (Real.rpow_nonneg hxpos.le δ)
  have hm := mul_le_mul hcoeff hlogbound (by linarith only [hlogq0, hlogh0]) hlarge
  have hmM := mul_le_mul_of_nonneg_right hm (regularizedLowHeightMajorant_nonneg (σ := σ) hx2)
  have hfin :=
    mul_le_mul_of_nonneg_left (rpow_log_low_majorant_le_common_weight hx2 hσ hbalance)
      (mul_nonneg (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 3) hK)
        (by linarith only [hlog2] : 0 ≤ 3 + Real.log 2))
  change
    (q : ℝ) * ((2 * R + 1) * K * (Real.log q + Real.log (4 + R) + 1)) *
        regularizedLowHeightMajorant x σ ≤
      _
  nlinarith only [hmM, hfin]

/-- Under the same level, scale, and exponent-balance conditions, the
level-weighted genus and arithmetic corrections plus the quadratic level-change
cost are bounded by one common power-log weight. Use `q <= R^2 <= x^delta`,
`q^2 <= R^2`, and logarithm monotonicity. This leaves only fixed constants in the
time-dependent part of the full family remainder. -/
theorem weighted_genus_and_arithmetic_corrections_le_common_weight {q H : ℕ} {x σ δ C : ℝ}
    (hq : 1 ≤ q) (hqr : q ≤ H + 1) (hx : 4 ≤ x) (hRx : ((H + 1 : ℕ) : ℝ) ≤ x)
    (hpow : ((H + 1 : ℕ) : ℝ) ^ 2 ≤ x ^ δ) (hσ : 1 / 2 ≤ σ) (hbalance : σ + 2 * δ ≤ 1)
    (hC : 0 ≤ C) :
    (q : ℝ) * (32 * Real.log 2) * (genusCorrectionBudgetConstant + Real.log q) +
        (q : ℝ) * C * (Real.log x + 1) +
        (q : ℝ) ^ 2 * (Real.log x) ^ 2 ≤
      ((32 * Real.log 2) * (genusCorrectionBudgetConstant + 1) + C + 1) *
        (x ^ (1 - δ) * (Real.log x + 1) ^ 3) := by
  let R : ℝ := ((H + 1 : ℕ) : ℝ)
  have hR : 1 ≤ R := by
    dsimp only [R]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le H)
  have hqR : (q : ℝ) ≤ R := Nat.cast_le.mpr hqr
  have hR2 : R ≤ R ^ 2 := by nlinarith only [hR, sq_nonneg (R - 1)]
  have hqδ : (q : ℝ) ≤ x ^ δ := (hqR.trans hR2).trans hpow
  have hq2 : (q : ℝ) ^ 2 ≤ x ^ δ := by
    have hp := mul_self_le_mul_self (Nat.cast_nonneg q) hqR
    nlinarith only [hp, hpow]
  have hx2 : 2 ≤ x := by linarith only [hx]
  have hxpos : 0 < x := by linarith only [hx]
  have hlog : 0 ≤ Real.log x := Real.log_nonneg (by linarith only [hx])
  have hlogq0 : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  have hlogq :=
    Real.log_le_log (by exact_mod_cast Nat.zero_lt_of_lt hq : (0 : ℝ) < q) (hqR.trans hRx)
  have hG : 0 ≤ genusCorrectionBudgetConstant := genusCorrectionBudgetConstant_pos.le
  have hgbound :
    genusCorrectionBudgetConstant + Real.log q ≤
      (genusCorrectionBudgetConstant + 1) * (Real.log x + 1) := by
    nlinarith only [hlogq, mul_nonneg hG hlog]
  have hcoef : 0 ≤ 32 * Real.log 2 :=
    mul_nonneg (by norm_num only) (Real.log_nonneg (by norm_num only))
  have hg := mul_le_mul hqδ hgbound (add_nonneg hG hlogq0) (Real.rpow_nonneg hxpos.le δ)
  have hg1 := mul_le_mul_of_nonneg_left hg hcoef
  have hweight := rpow_log_terms_le_common_weight hx2 hσ hbalance
  have hg2 :=
    mul_le_mul_of_nonneg_left hweight.1
      (mul_nonneg hcoef (by linarith only [hG] : 0 ≤ genusCorrectionBudgetConstant + 1))
  have hc1 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hqδ hC)
      (by linarith only [hlog] : 0 ≤ Real.log x + 1)
  have hc2 := mul_le_mul_of_nonneg_left hweight.1 hC
  have hl := (mul_le_mul_of_nonneg_right hq2 (sq_nonneg (Real.log x))).trans hweight.2
  nlinarith only [hg1, hg2, hc1, hc2, hl]

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
