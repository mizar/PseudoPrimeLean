/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaCheckpoint1000
public import PseudoPrime.PseudoSquare.Bounds.GammaSmallCheckpointBounds

/-! # Quadratic witness extraction using the certified cutoff-1000 prefix -/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- Input: GRH, an odd nonsquare n, log(n)<=L, x>=4096 and 1000<=b<=99x/40.
The signed dual cap and the explicit prefix margin must satisfy the displayed inequalities.
Claim: an odd prime negative Jacobi witness exists through 99x/40.
Proof: use the certified prefix margin and the actual factor-free witness criterion.
Role: remove an unproved boundary-tail input at the small analytic checkpoint. -/
theorem exists_prime_neg_one_witness_of_checkpoint1000 {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {b L x D : ℝ} (hb : 1000 ≤ b)
    (hD : LLS.gammaScaleSignedDualBudget L x ≤ D) (hL : 10 ≤ L) (hlog : Real.log n ≤ L)
    (hx : 4096 ≤ x) (hbx : b ≤ (99 / 40 : ℝ) * x)
    (hgap : 7 / 60 ≤ LLS.gammaPrefixSeparation L x D (203 / 50)) :
    ∃ q : ℕ, q.Prime ∧ Odd q ∧ (q : ℝ) ≤ (99 / 40 : ℝ) * x ∧ jacobiSym n q = -1 := by
  have hs := LLS.gamma_checkpoint1000_separation_le hGRH.riemann hb hD
  exact
    exists_prime_neg_one_witness_of_factor_free_separation hn hns hGRH hL hlog hx
      (by linarith only [hb]) hbx (hgap.trans hs)

/-- Input: GRH, a common log endpoint, an admissible scale and a cutoff-1000 margin.
Claim: the full negative-witness maximum is at most 99x/40.
Proof: transfer the certified prefix to the existing common-endpoint maximum theorem.
Role: include all smaller odd nonsquare inputs without a finite input search. -/
theorem QNegOne_le_of_checkpoint1000 {B : ℕ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {b x D : ℝ} (hb : 1000 ≤ b)
    (hD : LLS.gammaScaleSignedDualBudget (Real.log B) x ≤ D) (hL : 10 ≤ Real.log B) (hx : 4096 ≤ x)
    (hbx : b ≤ (99 / 40 : ℝ) * x)
    (hgap : 7 / 60 ≤ LLS.gammaPrefixSeparation (Real.log B) x D (203 / 50)) :
    (QNegOne B : ℝ) ≤ (99 / 40 : ℝ) * x := by
  have hs := LLS.gamma_checkpoint1000_separation_le hGRH.riemann hb hD
  exact QNegOne_le_of_factor_free_separation hGRH hL hx (by linarith only [hb]) hbx (hgap.trans hs)

/-- Input: the same cutoff, scale, dual-cap and margin conditions as for the negative maximum.
Claim: the full non-one maximum is at most 99x/40.
Proof: compare it with the negative maximum. Role: share the small-checkpoint improvement. -/
theorem QNeOne_le_of_checkpoint1000 {B : ℕ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {b x D : ℝ} (hb : 1000 ≤ b)
    (hD : LLS.gammaScaleSignedDualBudget (Real.log B) x ≤ D) (hL : 10 ≤ Real.log B) (hx : 4096 ≤ x)
    (hbx : b ≤ (99 / 40 : ℝ) * x)
    (hgap : 7 / 60 ≤ LLS.gammaPrefixSeparation (Real.log B) x D (203 / 50)) :
    (QNeOne B : ℝ) ≤ (99 / 40 : ℝ) * x := by
  have h := QNegOne_le_of_checkpoint1000 hGRH hb hD hL hx hbx hgap
  exact (Nat.cast_le.mpr (QNeOne_le_QNegOne B)).trans h

end PseudoPrime.PseudoSquare
