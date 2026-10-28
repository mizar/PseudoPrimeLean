/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.RefinedTheorem11S1
public import PseudoPrime.Analysis.RationalPart1Separation
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimeFactorSplitBounds
public import PseudoPrime.Analysis.RationalTheorem11S1

/-! # Rational Part 1 radius and universal logarithmic profile -/

@[expose] public section

namespace PseudoPrime.LLS

/-- For q ≥ 3000, the factor-sensitive rational radius is at most
log q+(1791/250)log log q+499/250. Split the prime support at (log q)^(5/8),
use the global logarithmic-power ratio and discard the nonnegative reciprocal saving.
This converts Part 1 to a single rational-coefficient expression. -/
theorem rationalRadiusRoot_le_logarithmic_shift {q : ℕ} [NeZero q] (hq : 3000 ≤ q) :
    rationalRadiusRoot q ≤ Real.log q + (1791 / 250 : ℝ) * Real.log (Real.log q) + 499 / 250 := by
  let L := Real.log q
  let z := Real.log L
  let u := L ^ (3 / 8 : ℝ)
  have hL8 := Analysis.eight_lt_log_level hq
  have hL : 1 < L := by linarith only [hL8]
  have hL0 : 0 < L := zero_lt_one.trans hL
  have hz0 : 0 < z := Real.log_pos hL
  have hu0 := Real.rpow_pos_of_pos hL0 (3 / 8 : ℝ)
  have hratio := Analysis.log_div_rpow_three_eighths_le hL0
  have hcard :=
    AnalyticNumberTheory.Arithmetic.primeFactors_card_le_log_power (NeZero.ne q) hL
      (by norm_num only : (0 : ℝ) < 5 / 8)
  have hpow : L ^ (5 / 8 : ℝ) = L / u := by
    apply (eq_div_iff hu0.ne').mpr
    rw [← Real.rpow_add hL0]
    norm_num only [Real.rpow_one]
  have hcan : L / ((5 / 8 : ℝ) * z) = (8 / 5 : ℝ) * L / z := by
    rw [div_mul_eq_div_div]
    ring
  change (q.primeFactors.card : ℝ) ≤ L ^ (5 / 8 : ℝ) + L / ((5 / 8 : ℝ) * z) at hcard
  rw [hpow, hcan] at hcard
  have hm := mul_le_mul_of_nonneg_right hcard (div_nonneg hz0.le hL0.le)
  have he : (L / u + (8 / 5 : ℝ) * L / z) * (z / L) = z / u + 8 / 5 := by
    calc
      _ = (z / u) * (L / L) + (8 / 5 : ℝ) * ((L / z) * z / L) := by ring
      _ = z / u + 8 / 5 := by
        rw [div_self hL0.ne', div_mul_cancel₀ _ hz0.ne', div_self hL0.ne', mul_one, mul_one]
  rw [he] at hm
  have hstep : (q.primeFactors.card : ℝ) * (z / L) ≤ 491 / 500 + 8 / 5 := by
    linarith only [hm, hratio]
  have hw := mul_le_mul_of_nonneg_left hstep (show 0 ≤ 2 * z by linarith only [hz0])
  have hwe :
    2 * z * ((q.primeFactors.card : ℝ) * (z / L)) = 2 * (q.primeFactors.card : ℝ) * z ^ 2 / L := by
    ring
  rw [hwe] at hw
  have hA : 0 ≤ refinedAuxiliaryTerm q := le_max_left _ _
  have hB : rationalCorrectionTerm q ≤ (1791 / 250 : ℝ) * z + 499 / 250 := by
    unfold rationalCorrectionTerm
    apply max_le (by linarith only [hz0])
    change
      2 * z + 499 / 250 + 2 * (q.primeFactors.card : ℝ) * z ^ 2 / L - 2 * refinedAuxiliaryTerm q ≤
        (1791 / 250 : ℝ) * z + 499 / 250
    linarith only [hw, hA]
  unfold rationalRadiusRoot
  linarith only [hB]

end PseudoPrime.LLS
