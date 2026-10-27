/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ParameterizedReciprocalLowerBound

/-! # Refined Euler, zero-mass and reciprocal constants for LLS -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Claim: the Euler constant is at most 0.57722.
Proof: combine the exact harmonic sum H_128 with the certified lower bound for log(128.5)
and the monotone midpoint approximation. Role: sharpen LLS reciprocal and zero-mass costs. -/
theorem eulerMascheroniConstant_le_28861_div_50000 :
    Real.eulerMascheroniConstant ≤ (28861 / 50000 : ℝ) := by
  have hh :
    harmonic 128 =
      (72552921080947538317446905633815133414572988188576608701 /
          13353756090997411579403749204440236542538872688049072000 :
        ℚ) := by
    decide +kernel
  have hc :
    rationalLogIntervalCheck (257 / 2) 7 12 (485592890 / 100000000) (485592891 / 100000000) =
      true := by
    decide +kernel
  have hl := (rationalLogIntervalCheck_sound hc).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hl
  have hg := eulerMascheroniConstant_le_midpoint 127
  norm_num only [midpointEulerSequence, hh, Rat.cast_div, Rat.cast_ofNat, Nat.reduceAdd,
    Nat.cast_ofNat] at hg
  linarith only [hl, hg]

end PseudoPrime.Analysis

namespace PseudoPrime.AnalyticNumberTheory.RiemannXi

/-- Claim: the Riemann zero mass is at most 0.0231.
Proof: insert the improved Euler bound and existing logarithm bounds into its closed formula.
Role: reduce the factorization-sensitive Part 1 correction. -/
theorem riemannZeroMass_le_231_div_10000 : riemannZeroMass ≤ (231 / 10000 : ℝ) := by
  have hlo := Analysis.log_pi_ge_2096_div_1831
  have hhi := Analysis.log_four_sub_log_pi_gt_twenty_four
  rw [Real.log_four_eq] at hhi
  rw [riemannZeroMass, abs_le, Real.log_mul (by norm_num only) Real.pi_ne_zero, Real.log_four_eq]
  constructor <;>
    nlinarith only [hlo, hhi, Real.log_two_gt_d9, Real.log_two_lt_d9,
      Real.one_half_lt_eulerMascheroniConstant, Analysis.eulerMascheroniConstant_le_28861_div_50000]

end PseudoPrime.AnalyticNumberTheory.RiemannXi

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Input: RH and a real cutoff at least two.
Claim: the reciprocal Mangoldt sum is at least log(x)-1.57755.
Proof: specialize the parameterized remainder with the refined Euler and zero-mass bounds.
Role: reduce the Part 2 correction without enumerating cutoffs. -/
theorem reciprocalWeightedMangoldtSum_ge_log_sub_31551_div_20000 (hRH : RiemannHypothesis) {x : ℝ}
    (hx : 2 ≤ x) :
    Real.log x - (31551 / 20000 : ℝ) ≤ Arithmetic.reciprocalWeightedMangoldtSum x := by
  have h :=
    reciprocalWeightedMangoldtSum_ge_of_parameters hRH hx
      Analysis.eulerMascheroniConstant_le_28861_div_50000 RiemannXi.riemannZeroMass_le_231_div_10000
      Analysis.log_two_mul_pi_gt.le (by norm_num only : (1 / 18 : ℝ) < 1837 / 1000)
  linarith only [h]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
