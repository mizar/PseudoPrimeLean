/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaAdaptiveCellTransfer
public import PseudoPrime.PseudoSquare.Bounds.GammaCheckpointBounds

/-! # Coefficient-parametric quadratic maximum bounds from checkpoint separation -/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- Input: GRH, a common logarithmic endpoint, scale and prefix admissibility, an actual
signed dual cap and checkpoint margin at least 7/60. Claim: the full negative maximum
is at most (99/40)*s*(log B)^2. Proof: use the common-endpoint checkpoint theorem.
Role: vary the witness coefficient through the kernel scale. -/
theorem QNegOne_le_scaled_log_sq_of_checkpoint {B : ℕ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {s D : ℝ} (hL : 10 ≤ Real.log B)
    (hx : 4096 ≤ s * (Real.log B) ^ 2) (hb : 50000 ≤ (99 / 40 : ℝ) * s * (Real.log B) ^ 2)
    (hD : LLS.gammaScaleSignedDualBudget (Real.log B) (s * (Real.log B) ^ 2) ≤ D)
    (hgap : 7 / 60 ≤ LLS.gammaCheckpointSeparation (Real.log B) (s * (Real.log B) ^ 2) D (33 / 5)) :
    (QNegOne B : ℝ) ≤ (99 / 40 : ℝ) * s * (Real.log B) ^ 2 := by
  have h :=
    QNegOne_le_of_checkpoint50000 hGRH hb hD hL hx
      (show (99 / 40 : ℝ) * s * (Real.log B) ^ 2 ≤ (99 / 40 : ℝ) * (s * (Real.log B) ^ 2) by
        exact le_of_eq (by ring))
      hgap
  nlinarith only [h]

/-- Input: the same certified endpoint with (99/40)*s<1.
Claim: the full negative maximum is strictly below (log B)^2.
Proof: retain the coefficient gap and positivity of the squared logarithm.
Role: distinguish strict subunit results from the coefficient-one endpoint. -/
theorem QNegOne_lt_log_sq_of_scaled_checkpoint {B : ℕ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {s D : ℝ} (hL : 10 ≤ Real.log B)
    (hs : (99 / 40 : ℝ) * s < 1) (hx : 4096 ≤ s * (Real.log B) ^ 2)
    (hb : 50000 ≤ (99 / 40 : ℝ) * s * (Real.log B) ^ 2)
    (hD : LLS.gammaScaleSignedDualBudget (Real.log B) (s * (Real.log B) ^ 2) ≤ D)
    (hgap : 7 / 60 ≤ LLS.gammaCheckpointSeparation (Real.log B) (s * (Real.log B) ^ 2) D (33 / 5)) :
    (QNegOne B : ℝ) < (Real.log B) ^ 2 := by
  have h := QNegOne_le_scaled_log_sq_of_checkpoint hGRH hL hx hb hD hgap
  have hpos := sq_pos_of_pos (show 0 < Real.log B by linarith only [hL])
  have hmul := mul_lt_mul_of_pos_right hs hpos
  nlinarith only [h, hmul]

/-- Input: GRH, log B>=225 and the actual dual and checkpoint-margin bounds at s=40/99.
Claim: the full negative maximum is at most (log B)^2.
Proof: verify scale/prefix admissibility and normalize the exact coefficient to one.
Role: expose coefficient-one improvement while keeping the remaining analytic obligations
explicit. -/
theorem QNegOne_le_log_sq_of_coefficient_one_checkpoint {B : ℕ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {D : ℝ} (hL : 225 ≤ Real.log B)
    (hD : LLS.gammaScaleSignedDualBudget (Real.log B) ((40 / 99 : ℝ) * (Real.log B) ^ 2) ≤ D)
    (hgap :
      7 / 60 ≤
        LLS.gammaCheckpointSeparation (Real.log B) ((40 / 99 : ℝ) * (Real.log B) ^ 2) D (33 / 5)) :
    (QNegOne B : ℝ) ≤ (Real.log B) ^ 2 := by
  have hsq := mul_nonneg (sub_nonneg.mpr hL) (show 0 ≤ Real.log B + 225 by linarith only [hL])
  have h :=
    QNegOne_le_scaled_log_sq_of_checkpoint hGRH (show 10 ≤ Real.log B by linarith only [hL])
      (show 4096 ≤ (40 / 99 : ℝ) * (Real.log B) ^ 2 by nlinarith only [hsq])
      (show 50000 ≤ (99 / 40 : ℝ) * (40 / 99) * (Real.log B) ^ 2 by nlinarith only [hsq]) hD hgap
  nlinarith only [h]

end PseudoPrime.PseudoSquare
