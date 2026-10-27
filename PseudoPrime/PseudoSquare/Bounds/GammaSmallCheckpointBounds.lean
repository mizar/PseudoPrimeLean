/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaSmallCheckpointBounds
public import PseudoPrime.PseudoSquare.Bounds.GammaCheckpointBounds

/-! # Quadratic witness interfaces from checkpoints starting at 100 -/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- Input: GRH, an odd nonsquare input, an admissible scale and a checkpoint a >= 100.
The boundary cap, dual cap and small-checkpoint margin must satisfy the displayed conditions.
Claim: an odd prime negative Jacobi witness exists through 99x/40.
Proof: transfer the small-checkpoint margin to the factor-free witness criterion.
Role: allow lower analytic cutoffs without an independent target error assumption. -/
theorem exists_prime_neg_one_witness_of_small_checkpoint {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {a b L x D : ℝ} {U : ℚ}
    (ha : 100 ≤ a) (hab : a ≤ b) (hU : LLS.gammaEulerBoundaryTail a ≤ (U : ℝ))
    (hD : LLS.gammaScaleSignedDualBudget L x ≤ D) (hL : 10 ≤ L) (hlog : Real.log n ≤ L)
    (hx : 4096 ≤ x) (hbx : b ≤ (99 / 40 : ℝ) * x)
    (hgap : 7 / 60 ≤ LLS.gammaPrefixSeparation L x D (1221 / 100 - U)) :
    ∃ q : ℕ, q.Prime ∧ Odd q ∧ (q : ℝ) ≤ (99 / 40 : ℝ) * x ∧ jacobiSym n q = -1 := by
  have hs := LLS.gamma_small_checkpoint_separation_le hGRH.riemann ha hab hU hD
  exact
    exists_prime_neg_one_witness_of_factor_free_separation hn hns hGRH hL hlog hx
      (by linarith only [ha, hab]) hbx (hgap.trans hs)

/-- Input: GRH, an admissible common log endpoint and a small-checkpoint separation certificate.
Claim: the full negative-witness maximum is at most 99x/40.
Proof: use the common-endpoint factor-free maximum theorem.
Role: include every smaller admissible input without enumerating it. -/
theorem QNegOne_le_of_small_checkpoint {B : ℕ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {a b x D : ℝ} {U : ℚ}
    (ha : 100 ≤ a) (hab : a ≤ b) (hU : LLS.gammaEulerBoundaryTail a ≤ (U : ℝ))
    (hD : LLS.gammaScaleSignedDualBudget (Real.log B) x ≤ D) (hL : 10 ≤ Real.log B) (hx : 4096 ≤ x)
    (hbx : b ≤ (99 / 40 : ℝ) * x)
    (hgap : 7 / 60 ≤ LLS.gammaPrefixSeparation (Real.log B) x D (1221 / 100 - U)) :
    (QNegOne B : ℝ) ≤ (99 / 40 : ℝ) * x := by
  have hs := LLS.gamma_small_checkpoint_separation_le hGRH.riemann ha hab hU hD
  exact
    QNegOne_le_of_factor_free_separation hGRH hL hx (by linarith only [ha, hab]) hbx (hgap.trans hs)

/-- Input: the same common-endpoint assumptions as for the negative maximum.
Claim: the full non-one maximum is at most 99x/40.
Proof: compare the two maxima. Role: share the small-checkpoint analytic improvement. -/
theorem QNeOne_le_of_small_checkpoint {B : ℕ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {a b x D : ℝ} {U : ℚ}
    (ha : 100 ≤ a) (hab : a ≤ b) (hU : LLS.gammaEulerBoundaryTail a ≤ (U : ℝ))
    (hD : LLS.gammaScaleSignedDualBudget (Real.log B) x ≤ D) (hL : 10 ≤ Real.log B) (hx : 4096 ≤ x)
    (hbx : b ≤ (99 / 40 : ℝ) * x)
    (hgap : 7 / 60 ≤ LLS.gammaPrefixSeparation (Real.log B) x D (1221 / 100 - U)) :
    (QNeOne B : ℝ) ≤ (99 / 40 : ℝ) * x := by
  have h := QNegOne_le_of_small_checkpoint hGRH ha hab hU hD hL hx hbx hgap
  exact (Nat.cast_le.mpr (QNeOne_le_QNegOne B)).trans h

end PseudoPrime.PseudoSquare
