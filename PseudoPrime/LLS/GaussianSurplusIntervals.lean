/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.FiniteSignedEulerIntervals
public import PseudoPrime.Analysis.GaussianGammaWeightComparison
public import PseudoPrime.Analysis.GammaEulerSeed100

/-! # Integer power intervals for the finite Gaussian surplus -/

@[expose] public section

namespace PseudoPrime.LLS

/-- The eighteen nonzero aggregated Gaussian-minus-seventeen-twentieths-Gamma nodes.
Each node lies on the denominator-200 grid; the sum equality is proved below. -/
def gaussianSurplusCoefficients : List (ℚ × ℚ) :=
  [(11 / 20, 284090057 / 2000000000), (139 / 200, 23848901 / 100000000),
    (4 / 5, -286385043 / 2000000000), (7 / 8, -171023537 / 100000000), (1, -111201233 / 250000000),
    (11 / 10, 89949413 / 10000000), (277 / 200, -2075895953 / 100000000),
    (17 / 10, -614332179 / 500000000), (7 / 4, 4073757753 / 100000000),
    (441 / 200, -362665019 / 6250000), (23 / 10, 3515093349 / 2000000000),
    (111 / 40, 977148369 / 20000000), (16 / 5, 17955179 / 200000000),
    (7 / 2, -487729179 / 20000000), (441 / 100, 745378529 / 100000000),
    (9 / 2, -425241723 / 1000000000), (1111 / 200, -16529553 / 12500000), (7, 2849561 / 16000000)]

/-- Aggregating equal nodes and removing zero coefficients preserves the actual Euler weight.
Expand both finite lists and use exact coefficient arithmetic. -/
theorem gaussianSurplus_euler_eq (m : ℝ) :
    Analysis.finiteSignedEulerWeight gaussianSurplusCoefficients m =
      Analysis.gaussianResolventEulerWeight m -
        (17 / 20 : ℝ) * Analysis.gammaResolventEulerWeight m := by
  norm_num only [Analysis.finiteSignedEulerWeight, gaussianSurplusCoefficients,
    Analysis.gaussianResolventEulerWeight, Analysis.gammaResolventEulerWeight,
    Analysis.gaussianResolventCoefficients, AnalyticNumberTheory.Gamma.gammaResolventCoefficients,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Rat.cast_div, Rat.cast_ofNat,
    Rat.cast_neg]
  ring

/-- Two natural-number power inequalities certify the real power interval with denominator ten
million and exponent denominator 200. Cast the checks and apply natural-power monotonicity. -/
theorem gaussianSurplus_nat_interval {m e q : ℕ} (hm : 0 < m)
    (hl : q ^ 200 * m ^ e ≤ (10000000 : ℕ) ^ 200)
    (hu : (10000000 : ℕ) ^ 200 ≤ (q + 1) ^ 200 * m ^ e) :
    (q : ℝ) / 10000000 ≤ (m : ℝ) ^ (-(e : ℝ) / 200) ∧
      (m : ℝ) ^ (-(e : ℝ) / 200) ≤ ((q + 1 : ℕ) : ℝ) / 10000000 := by
  have hlR : (q : ℝ) ^ 200 * (m : ℝ) ^ e ≤ (10000000 : ℝ) ^ 200 := by
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using (Nat.cast_le (α := ℝ)).mpr hl
  have huR : (10000000 : ℝ) ^ 200 ≤ ((q + 1 : ℕ) : ℝ) ^ 200 * (m : ℝ) ^ e := by
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using (Nat.cast_le (α := ℝ)).mpr hu
  have hB : 0 < (10000000 : ℝ) ^ 200 := pow_pos (by norm_num only) _
  have hmul (a : ℝ) :
    (a / 10000000) ^ 200 * (m : ℝ) ^ e = (a ^ 200 * (m : ℝ) ^ e) / (10000000 : ℝ) ^ 200 := by
    rw [div_pow]
    ring
  apply
    Analysis.rpow_neg_div_nat_interval (Nat.cast_pos.mpr hm)
      (div_nonneg (Nat.cast_nonneg _) (by norm_num only))
      (div_nonneg (Nat.cast_nonneg _) (by norm_num only)) e 200 (by decide)
  · rw [hmul]
    exact (div_le_one hB).mpr hlR
  · rw [hmul]
    exact (one_le_div hB).mpr huR

end PseudoPrime.LLS
