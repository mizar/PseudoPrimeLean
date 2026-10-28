/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaUniformSignedShiftBounds
public import PseudoPrime.LLS.PaperStatements.GammaUniformSmallScaleNumerics

/-! # Uniform Gamma numerical budgets from scale 224 -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For nonzero q, T > 1, log q ≤ T, positive x and cutoff X ≥ 1,
a root lower coefficient a > 0, log X ≤ 2 log T and cube-root ratio beta give
twice the normalized nonunit loss at most (4/a)(beta+3/2).
Split the prime support at T^(2/3) and use the ambient logarithm upper bound.
This permits small logarithmic inputs with a larger shifted scale. -/
theorem gamma_commonFactor_budget_of_ambient_scale {q : ℕ} [NeZero q] {T x X a beta : ℝ}
    (ha : 0 < a) (hL : 1 < T) (hambient : Real.log q ≤ T) (hx0 : 0 < x) (hcut : 1 ≤ X)
    (hcutlog : Real.log X ≤ 2 * Real.log T) (hroot : a * T ≤ Real.sqrt x)
    (hlog : Real.log T / (T) ^ (1 / 3 : ℝ) ≤ beta) :
    2 * (AnalyticNumberTheory.Arithmetic.commonFactorExponentialSum x X q / Real.sqrt x) ≤
      (4 / a) * (beta + 3 / 2) := by
  let L := T
  have hL0 : 0 < L := zero_lt_one.trans hL
  have hs0 := Real.sqrt_pos.mpr hx0
  have hu0 := Real.rpow_pos_of_pos hL0 (1 / 3 : ℝ)
  have hlog0 := Real.log_pos hL
  have hp : L ^ (2 / 3 : ℝ) = L / L ^ (1 / 3 : ℝ) := by
    apply (eq_div_iff hu0.ne').mpr
    rw [← Real.rpow_add hL0]
    norm_num only [Real.rpow_one]
  have hc := hcutlog
  have hF0 : 0 ≤ L ^ (2 / 3 : ℝ) + (3 / 2 : ℝ) * L / Real.log L :=
    add_nonneg (Real.rpow_pos_of_pos hL0 _).le (div_nonneg (by linarith only [hL0]) hlog0.le)
  have hcard :=
    AnalyticNumberTheory.Arithmetic.primeFactors_card_le_cutoff_add_log_div (NeZero.ne q)
      (Real.one_lt_rpow hL (by norm_num only : (0 : ℝ) < 2 / 3))
  rw [Real.log_rpow hL0] at hcard
  have hdiv :=
    div_le_div_of_nonneg_right hambient (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2 / 3) hlog0.le)
  have hcancel : L / ((2 / 3 : ℝ) * Real.log L) = (3 / 2 : ℝ) * L / Real.log L := by
    rw [div_mul_eq_div_div]
    ring
  have hF : (q.primeFactors.card : ℝ) ≤ L ^ (2 / 3 : ℝ) + (3 / 2 : ℝ) * L / Real.log L := by
    rw [hcancel] at hdiv
    linarith only [hcard, hdiv]
  have hnum :=
    (AnalyticNumberTheory.Arithmetic.commonFactorExponentialSum_le_card_mul_log (NeZero.ne q) hx0
          hcut).trans
      ((mul_le_mul_of_nonneg_right hF (Real.log_nonneg hcut)).trans
        (mul_le_mul_of_nonneg_left hc hF0))
  have he :
    (L ^ (2 / 3 : ℝ) + (3 / 2 : ℝ) * L / Real.log L) * (2 * Real.log L) =
      2 * L * (Real.log L / L ^ (1 / 3 : ℝ) + 3 / 2) := by
    rw [hp]
    have hbcan : ((3 / 2 : ℝ) * L / Real.log L) * (2 * Real.log L) = 3 * L := by
      calc
        _ = 2 * ((3 / 2 : ℝ) * L / Real.log L * Real.log L) := by ring
        _ = 2 * ((3 / 2 : ℝ) * L) := by rw [div_mul_cancel₀ _ hlog0.ne']
        _ = 3 * L := by ring
    rw [add_mul, hbcan]
    ring
  change
    AnalyticNumberTheory.Arithmetic.commonFactorExponentialSum x X q ≤
      (L ^ (2 / 3 : ℝ) + (3 / 2 : ℝ) * L / Real.log L) * (2 * Real.log L) at hnum
  rw [he] at hnum
  have hB0 : 0 ≤ Real.log L / L ^ (1 / 3 : ℝ) + 3 / 2 :=
    add_nonneg (div_nonneg hlog0.le hu0.le) (by norm_num only)
  have hr : L / Real.sqrt x ≤ 1 / a := by
    apply (div_le_div_iff₀ hs0 ha).mpr
    nlinarith only [hroot]
  have hm := mul_le_mul_of_nonneg_left hr (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 4) hB0)
  have ht :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hnum (by norm_num only : (0 : ℝ) ≤ 2))
      (Real.sqrt_nonneg x)
  calc
    _ = 2 * AnalyticNumberTheory.Arithmetic.commonFactorExponentialSum x X q / Real.sqrt x := by
      ring
    _ ≤ 2 * (2 * L * (Real.log L / L ^ (1 / 3 : ℝ) + 3 / 2)) / Real.sqrt x := ht
    _ = 4 * (Real.log L / L ^ (1 / 3 : ℝ) + 3 / 2) * (L / Real.sqrt x) := by ring
    _ ≤ 4 * (Real.log L / L ^ (1 / 3 : ℝ) + 3 / 2) * (1 / a) := hm
    _ = (4 / a) * (Real.log L / L ^ (1 / 3 : ℝ) + 3 / 2) := by ring
    _ ≤ (4 / a) * (beta + 3 / 2) :=
      mul_le_mul_of_nonneg_left (add_le_add_left hlog (3 / 2 : ℝ))
        (div_nonneg (by norm_num only : (0 : ℝ) ≤ 4) ha.le)

end PseudoPrime.Analysis
