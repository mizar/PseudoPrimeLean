/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannXi.FinerLLSConstants

/-! # Pointwise reciprocal losses retaining the scale-dependent terms -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Input: RH, cutoff at least two, and bounds for Euler's constant, zero mass and log(2 pi).
Claim: the reciprocal sum retains its positive inverse-cutoff and negative inverse-root terms.
Proof: bound the trivial-zero tail geometrically before any square completion.
Role: expose cutoff-dependent savings for both witness comparisons. -/
theorem reciprocalWeightedMangoldtSum_ge_pointwise_of_parameters (hRH : RiemannHypothesis)
    {x G B P : ℝ} (hx : 2 ≤ x) (hG : Real.eulerMascheroniConstant ≤ G)
    (hB : RiemannXi.riemannZeroMass ≤ B) (hP : P ≤ Real.log (2 * Real.pi)) :
    Real.log x - (1 + G) - 2 * B / Real.sqrt x + (P - 1 / 18) / x ≤
      Arithmetic.reciprocalWeightedMangoldtSum x := by
  have hxp : 0 < x := lt_of_lt_of_le (by norm_num only) hx
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hxp
  have ht :=
    (riemannReciprocalTrivialZeroSeries_le_geometric hx).trans
      (Analysis.geometricTail_le_one_div_eighteen_mul hx)
  rw [div_mul_eq_div_div] at ht
  have hz :=
    (div_le_div_iff_of_pos_right hs).mpr
      (mul_le_mul_of_nonneg_left hB (by norm_num only : (0 : ℝ) ≤ 2))
  have hl := div_le_div_of_nonneg_right hP hxp.le
  have heq := reciprocalWeightedMangoldtSum_eq_integral hxp (τ := 2) (by norm_num only)
  have hre := congrArg Complex.re heq
  rw [Complex.ofReal_re] at hre
  simp only [Complex.ofReal_ofNat] at hre
  rw [hre]
  have hf :=
    re_integral_riemannZetaReciprocalContourKernel_two_ge_of_riemannHypothesis hRH
      (lt_of_lt_of_le (by norm_num only) hx)
  simp only [div_eq_mul_inv] at ht hz hl hf ⊢
  nlinarith only [hf, ht, hz, hl, hG]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta

namespace PseudoPrime.Analysis

/-- Input: a real root y. Output: the rational reciprocal loss 1.57722+0.0462/y-(16033/9000)/y^2.
Role: retain the scale dependence before passing to a uniform reciprocal constant. -/
noncomputable def pointwiseReciprocalLoss (y : ℝ) : ℝ :=
  78861 / 50000 + (231 / 5000) / y - (16033 / 9000) / y ^ 2

/-- Input: a root at least seven. Claim: its pointwise reciprocal loss is at least 3/2.
Proof: bound the negative inverse-square term at seven and retain the positive term.
Role: supply the scalar separation's lower loss requirement. -/
theorem pointwiseReciprocalLoss_ge_three_halves {y : ℝ} (hy : 7 ≤ y) :
    (3 / 2 : ℝ) ≤ pointwiseReciprocalLoss y := by
  have hsq : (49 : ℝ) ≤ y ^ 2 := by nlinarith only [hy]
  have hn : 0 ≤ (231 / 5000 : ℝ) / y := div_nonneg (by norm_num only) (by linarith only [hy])
  have hk :=
    div_le_div_of_nonneg_left (by norm_num only : (0 : ℝ) ≤ 16033 / 9000)
      (by norm_num only : (0 : ℝ) < 49) hsq
  dsimp only [pointwiseReciprocalLoss]
  linarith only [hn, hk]

/-- Input: any real root. Claim: its pointwise loss is at most 31551/20000.
Proof: complete the quadratic in its reciprocal explicitly.
Role: compare the adaptive loss with the established uniform theorem. -/
theorem pointwiseReciprocalLoss_le_uniform (y : ℝ) :
    pointwiseReciprocalLoss y ≤ (31551 / 20000 : ℝ) := by
  have h :=
    quadratic_remainder_lower (a := (16033 / 9000 : ℝ)) (b := (231 / 10000 : ℝ)) (u := 1 / y)
      (by norm_num only)
  dsimp only [pointwiseReciprocalLoss]
  rw [show (1 / y) ^ 2 = 1 / y ^ 2 by rw [div_pow, one_pow]] at h
  simp only [div_eq_mul_inv] at h ⊢
  nlinarith only [h]

end PseudoPrime.Analysis

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Input: RH, a positive root, and its square at least two.
Claim: the reciprocal Mangoldt sum is at least log(y^2) minus the pointwise loss.
Proof: specialize the parameterized pointwise bound with the finest proved constants.
Role: provide the actual arithmetic input for adaptive-radius witnesses. -/
theorem reciprocalWeightedMangoldtSum_ge_pointwise_loss (hRH : RiemannHypothesis) {y : ℝ}
    (hy : 0 < y) (hx : 2 ≤ y ^ 2) :
    Real.log (y ^ 2) - Analysis.pointwiseReciprocalLoss y ≤
      Arithmetic.reciprocalWeightedMangoldtSum (y ^ 2) := by
  have h :=
    reciprocalWeightedMangoldtSum_ge_pointwise_of_parameters hRH hx
      Analysis.eulerMascheroniConstant_le_28861_div_50000 RiemannXi.riemannZeroMass_le_231_div_10000
      Analysis.log_two_mul_pi_gt.le
  rw [Real.sqrt_sq hy.le] at h
  dsimp only [Analysis.pointwiseReciprocalLoss]
  simp only [div_eq_mul_inv] at h ⊢
  nlinarith only [h]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
