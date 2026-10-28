/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannXi.FinerLLSConstants
public import PseudoPrime.Analysis.PointwiseReciprocalLowerBound

/-! # Pointwise reciprocal losses retaining the scale-dependent terms -/

@[expose] public section

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
