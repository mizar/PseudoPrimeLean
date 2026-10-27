/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaCheckpoint50000
public import PseudoPrime.PseudoSquare.Bounds.GammaFactorFreeBounds

/-! # Quadratic witness bounds from arbitrary Euler-boundary checkpoints -/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- Input: GRH, odd nonsquare n, an admissible scale, a checked boundary checkpoint,
a dual upper cap and checkpoint margin at least 7/60. Claim: a negative odd-prime witness
exists through 99x/40. Proof: transfer to the factor-free criterion. Role: witness extraction. -/
theorem exists_prime_neg_one_witness_of_checkpoint {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {a b L x D : ℝ} {U : ℚ}
    (ha : 50000 ≤ a) (hab : a ≤ b) (hU : LLS.gammaEulerBoundaryTail a ≤ (U : ℝ))
    (hD : LLS.gammaScaleSignedDualBudget L x ≤ D) (hL : 10 ≤ L) (hlog : Real.log n ≤ L)
    (hx : 4096 ≤ x) (hbx : b ≤ (99 / 40 : ℝ) * x)
    (hgap : 7 / 60 ≤ LLS.gammaCheckpointSeparation L x D U) :
    ∃ q : ℕ, q.Prime ∧ Odd q ∧ (q : ℝ) ≤ (99 / 40 : ℝ) * x ∧ jacobiSym n q = -1 := by
  have hs := LLS.gamma_checkpoint_separation_le hGRH.riemann ha hab hU hD
  exact
    exists_prime_neg_one_witness_of_factor_free_separation hn hns hGRH hL hlog hx
      (by linarith only [ha, hab]) hbx (hgap.trans hs)

/-- Input: GRH, a common log B endpoint and the same checkpoint separation hypotheses.
Claim: the full negative-witness maximum through B is at most 99x/40.
Proof: use the common-endpoint factor-free theorem. Role: include all smaller inputs. -/
theorem QNegOne_le_of_checkpoint {B : ℕ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {a b x D : ℝ} {U : ℚ}
    (ha : 50000 ≤ a) (hab : a ≤ b) (hU : LLS.gammaEulerBoundaryTail a ≤ (U : ℝ))
    (hD : LLS.gammaScaleSignedDualBudget (Real.log B) x ≤ D) (hL : 10 ≤ Real.log B) (hx : 4096 ≤ x)
    (hbx : b ≤ (99 / 40 : ℝ) * x)
    (hgap : 7 / 60 ≤ LLS.gammaCheckpointSeparation (Real.log B) x D U) :
    (QNegOne B : ℝ) ≤ (99 / 40 : ℝ) * x := by
  have hs := LLS.gamma_checkpoint_separation_le hGRH.riemann ha hab hU hD
  exact
    QNegOne_le_of_factor_free_separation hGRH hL hx (by linarith only [ha, hab]) hbx (hgap.trans hs)

/-- Input: the same checkpoint hypotheses under GRH. Claim: the full non-one-witness
maximum is at most 99x/40. Proof: compare the two maxima. Role: cover both quadratic maxima. -/
theorem QNeOne_le_of_checkpoint {B : ℕ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {a b x D : ℝ} {U : ℚ}
    (ha : 50000 ≤ a) (hab : a ≤ b) (hU : LLS.gammaEulerBoundaryTail a ≤ (U : ℝ))
    (hD : LLS.gammaScaleSignedDualBudget (Real.log B) x ≤ D) (hL : 10 ≤ Real.log B) (hx : 4096 ≤ x)
    (hbx : b ≤ (99 / 40 : ℝ) * x)
    (hgap : 7 / 60 ≤ LLS.gammaCheckpointSeparation (Real.log B) x D U) :
    (QNeOne B : ℝ) ≤ (99 / 40 : ℝ) * x := by
  have h := QNegOne_le_of_checkpoint hGRH ha hab hU hD hL hx hbx hgap
  exact (Nat.cast_le.mpr (QNeOne_le_QNegOne B)).trans h

/-- Input: GRH, b>=50000, an admissible common scale and a certified checkpoint margin.
Claim: the full negative-witness maximum is at most 99x/40.
Proof: use the fully proved checkpoint tail bound. Role: remove the boundary-tail assumption. -/
theorem QNegOne_le_of_checkpoint50000 {B : ℕ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {b x D : ℝ} (hb : 50000 ≤ b)
    (hD : LLS.gammaScaleSignedDualBudget (Real.log B) x ≤ D) (hL : 10 ≤ Real.log B) (hx : 4096 ≤ x)
    (hbx : b ≤ (99 / 40 : ℝ) * x)
    (hgap : 7 / 60 ≤ LLS.gammaCheckpointSeparation (Real.log B) x D (33 / 5)) :
    (QNegOne B : ℝ) ≤ (99 / 40 : ℝ) * x := by
  have hs := LLS.gamma_checkpoint50000_separation_le hGRH.riemann hb hD
  exact QNegOne_le_of_factor_free_separation hGRH hL hx (by linarith only [hb]) hbx (hgap.trans hs)

/-- Input: the same certified scale under GRH.
Claim: the full non-one-witness maximum is at most 99x/40.
Proof: compare with the negative maximum. Role: remove the boundary field for both maxima. -/
theorem QNeOne_le_of_checkpoint50000 {B : ℕ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {b x D : ℝ} (hb : 50000 ≤ b)
    (hD : LLS.gammaScaleSignedDualBudget (Real.log B) x ≤ D) (hL : 10 ≤ Real.log B) (hx : 4096 ≤ x)
    (hbx : b ≤ (99 / 40 : ℝ) * x)
    (hgap : 7 / 60 ≤ LLS.gammaCheckpointSeparation (Real.log B) x D (33 / 5)) :
    (QNeOne B : ℝ) ≤ (99 / 40 : ℝ) * x := by
  have h := QNegOne_le_of_checkpoint50000 hGRH hb hD hL hx hbx hgap
  exact (Nat.cast_le.mpr (QNeOne_le_QNegOne B)).trans h

end PseudoPrime.PseudoSquare
