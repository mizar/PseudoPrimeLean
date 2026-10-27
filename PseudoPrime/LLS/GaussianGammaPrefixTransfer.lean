/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GaussianGammaWeightComparison
public import PseudoPrime.Analysis.GaussianSignedEulerSeries
public import PseudoPrime.Analysis.GammaSignedEulerSeries
public import PseudoPrime.LLS.GammaCheckpoint1000
public import PseudoPrime.LLS.RiemannOneSidedCheckpoint

/-! # Transfer of the Gamma prefix to the Gaussian Euler weight -/

@[expose] public section

namespace PseudoPrime.LLS

/-- At each natural input, the Gaussian Mangoldt weight is at least seventeen
twentieths of the Gamma Mangoldt weight. The zero input vanishes, and positive
inputs follow from the real Euler weight comparison and nonnegative Mangoldt value. -/
theorem gaussian_gamma_mangoldt_weight_le (n : ℕ) :
    (17 / 20 : ℝ) * Analysis.gammaResolventMangoldtWeight n ≤
      Analysis.gaussianResolventMangoldtWeight n := by
  rw [Analysis.gaussianResolventMangoldtWeight, Analysis.gammaResolventMangoldtWeight]
  rcases Nat.eq_zero_or_pos n with h | h
  · simp only [h, ArithmeticFunction.map_zero, zero_mul, mul_zero, le_rfl]
  · have hw := Analysis.gaussianGamma_weight_difference_nonneg (Nat.one_le_cast.mpr h)
    have hweight :
      (17 / 20 : ℝ) * Analysis.gammaResolventEulerWeight (n : ℝ) ≤
        Analysis.gaussianResolventEulerWeight (n : ℝ) := by
      linarith only [hw]
    have hΛ := ArithmeticFunction.vonMangoldt_nonneg (n := n)
    have hmul := mul_le_mul_of_nonneg_left hweight hΛ
    change
      (17 / 20 : ℝ) *
          (ArithmeticFunction.vonMangoldt n * Analysis.gammaResolventEulerWeight (n : ℝ)) ≤
        ArithmeticFunction.vonMangoldt n * Analysis.gaussianResolventEulerWeight (n : ℝ)
    calc
      (17 / 20 : ℝ) *
            (ArithmeticFunction.vonMangoldt n * Analysis.gammaResolventEulerWeight (n : ℝ)) =
          ArithmeticFunction.vonMangoldt n *
            ((17 / 20 : ℝ) * Analysis.gammaResolventEulerWeight (n : ℝ)) :=
        by ring
      _ ≤ ArithmeticFunction.vonMangoldt n * Analysis.gaussianResolventEulerWeight (n : ℝ) := hmul

/-- Under RH, the Gaussian prefix from 50000 onward is at least 484381/100000.
Scale the Gamma prefix lower bound by seventeen twentieths, then sum the pointwise
Mangoldt weight comparison over the same finite interval. -/
theorem gaussian_prefix50000_lower {b : ℝ} (hRH : RiemannHypothesis) (hb : 50000 ≤ b) :
    (484381 / 100000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gaussianResolventMangoldtWeight n := by
  have hgamma := gamma_prefix50000_lower_asymmetric hRH hb
  have hsum :=
    Finset.sum_le_sum (s := Finset.Ioc 0 ⌊b⌋₊) (fun n _ ↦ gaussian_gamma_mangoldt_weight_le n)
  have hsum' :
    (17 / 20 : ℝ) * (∑ n ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight n) ≤
      ∑ n ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gaussianResolventMangoldtWeight n := by
    simpa only [Finset.mul_sum] using hsum
  have hscaled := mul_le_mul_of_nonneg_left hgamma (by norm_num only : (0 : ℝ) ≤ 17 / 20)
  norm_num only at hscaled
  exact hscaled.trans hsum'

/-- Under RH, the Gaussian prefix from 1000 onward has mass at least
3451/1000. Transfer the Gamma 1000-prefix lower bound through the pointwise
Gaussian-to-Gamma Mangoldt weight comparison. -/
theorem gaussian_prefix1000_lower {b : ℝ} (hRH : RiemannHypothesis) (hb : 1000 ≤ b) :
    (3451 / 1000 : ℝ) ≤ ∑ n ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gaussianResolventMangoldtWeight n := by
  have hgamma := gamma_prefix1000_lower_halfline hRH hb
  have hsum :=
    Finset.sum_le_sum (s := Finset.Ioc 0 ⌊b⌋₊) (fun n _ ↦ gaussian_gamma_mangoldt_weight_le n)
  have hsum' :
    (17 / 20 : ℝ) * (∑ n ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight n) ≤
      ∑ n ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gaussianResolventMangoldtWeight n := by
    simpa only [Finset.mul_sum] using hsum
  have hscaled := mul_le_mul_of_nonneg_left hgamma (by norm_num only : (0 : ℝ) ≤ 17 / 20)
  norm_num only at hscaled
  exact hscaled.trans hsum'

end PseudoPrime.LLS
