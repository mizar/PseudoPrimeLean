/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.RiemannOneSidedCheckpoint
public import PseudoPrime.PseudoSquare.Bounds.GammaCheckpointBounds

/-! # Quadratic witness interfaces with the asymmetric Euler checkpoint -/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- Input: GRH, an odd nonsquare input, admissible scale and a signed dual cap.
The refined checkpoint margin must be at least 7/60.
Claim: an odd prime negative witness exists through 99x/40.
Proof: use the proved asymmetric checkpoint tail in the generic witness theorem.
Role: expose the improved prefix estimate to actual quadratic witnesses. -/
theorem exists_prime_neg_one_witness_of_asymmetric_checkpoint {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {b L x D : ℝ}
    (hb : 50000 ≤ b) (hD : LLS.gammaScaleSignedDualBudget L x ≤ D) (hL : 10 ≤ L)
    (hlog : Real.log n ≤ L) (hx : 4096 ≤ x) (hbx : b ≤ (99 / 40 : ℝ) * x)
    (hgap : 7 / 60 ≤ LLS.gammaCheckpointSeparation L x D (3293 / 500)) :
    ∃ q : ℕ, q.Prime ∧ Odd q ∧ (q : ℝ) ≤ (99 / 40 : ℝ) * x ∧ jacobiSym n q = -1 := by
  have hs := LLS.gamma_checkpoint50000_asymmetric_separation_le hGRH.riemann hb hD
  exact
    exists_prime_neg_one_witness_of_factor_free_separation hn hns hGRH hL hlog hx
      (by linarith only [hb]) hbx (hgap.trans hs)

/-- Input: GRH, an admissible common log endpoint and the refined checkpoint margin.
Claim: the full negative-witness maximum through B is at most 99x/40.
Proof: transfer the proved checkpoint to the common-endpoint maximum theorem.
Role: include all smaller admissible inputs without enumerating them. -/
theorem QNegOne_le_of_asymmetric_checkpoint {B : ℕ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {b x D : ℝ} (hb : 50000 ≤ b)
    (hD : LLS.gammaScaleSignedDualBudget (Real.log B) x ≤ D) (hL : 10 ≤ Real.log B) (hx : 4096 ≤ x)
    (hbx : b ≤ (99 / 40 : ℝ) * x)
    (hgap : 7 / 60 ≤ LLS.gammaCheckpointSeparation (Real.log B) x D (3293 / 500)) :
    (QNegOne B : ℝ) ≤ (99 / 40 : ℝ) * x := by
  have hs := LLS.gamma_checkpoint50000_asymmetric_separation_le hGRH.riemann hb hD
  exact QNegOne_le_of_factor_free_separation hGRH hL hx (by linarith only [hb]) hbx (hgap.trans hs)

/-- Input: the same GRH, scale, dual and margin assumptions as for the negative maximum.
Claim: the full non-one maximum through B is at most 99x/40.
Proof: compare the two maxima and apply the refined negative-witness bound.
Role: share the analytic improvement between both quadratic witness problems. -/
theorem QNeOne_le_of_asymmetric_checkpoint {B : ℕ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {b x D : ℝ} (hb : 50000 ≤ b)
    (hD : LLS.gammaScaleSignedDualBudget (Real.log B) x ≤ D) (hL : 10 ≤ Real.log B) (hx : 4096 ≤ x)
    (hbx : b ≤ (99 / 40 : ℝ) * x)
    (hgap : 7 / 60 ≤ LLS.gammaCheckpointSeparation (Real.log B) x D (3293 / 500)) :
    (QNeOne B : ℝ) ≤ (99 / 40 : ℝ) * x := by
  have h := QNegOne_le_of_asymmetric_checkpoint hGRH hb hD hL hx hbx hgap
  exact (Nat.cast_le.mpr (QNeOne_le_QNegOne B)).trans h

end PseudoPrime.PseudoSquare
