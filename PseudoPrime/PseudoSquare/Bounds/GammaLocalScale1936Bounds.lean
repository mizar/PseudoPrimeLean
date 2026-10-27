/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaLocalScale1936
public import PseudoPrime.LLS.GammaCertifiedLocalBridge
public import PseudoPrime.PseudoSquare.Bounds.GammaCheckpoint1000Bounds

/-! # Quadratic witness interfaces from actual local scale certificates -/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- Input: GRH, an odd nonsquare input, scale x>=2, a local certificate and a valid prefix.
Claim: scalar gap at least delta-3/4 yields an odd-prime negative Jacobi witness.
Proof: choose the common auxiliary pole level and transfer to actual separation.
Role: replace the fixed scale gate by a complete actual local certificate. -/
theorem exists_prime_neg_one_witness_of_local_certificate {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {L b x δ : ℝ} (hL : 10 ≤ L)
    (hlog : Real.log n ≤ L) (hx : 2 ≤ x) (cert : Analysis.GammaLocalBudgetCertificate x δ)
    (hb : 1 ≤ b) (hbx : b ≤ (99 / 40 : ℝ) * x)
    (hgap : δ - 3 / 4 ≤ LLS.gammaFactorFreeSeparation L b x) :
    ∃ q : ℕ, q.Prime ∧ Odd q ∧ (q : ℝ) ≤ (99 / 40 : ℝ) * x ∧ jacobiSym n q = -1 := by
  let Q := max 20000 (4 * n)
  have hQ : 20000 ≤ Q := le_max_left _ _
  have hnQ : 4 * n ≤ Q := le_max_right _ _
  have hlogQ := LLS.gamma_log_pole_level_le_of_common_endpoint hn hL hlog
  have hs :=
    LLS.gamma_factor_free_separation_of_local_certificate (Q := Q) (b := b) hn hns hlog cert hlogQ
  have hg :
    0 ≤
      LLS.gammaJointPrefixSeparation Q (NumberTheory.complexQuadraticCharacter n hn) b x
        (-3 / 2) := by
    linarith only [hs, hgap]
  exact exists_prime_neg_one_witness_of_joint_prefix_separation hn hns hQ hnQ hGRH hx hb hbx hg

/-- Input: GRH, a common log endpoint, local certificate and scalar gap.
Claim: the full negative-witness maximum is at most 99x/40.
Proof: apply the certified witness criterion to every admissible smaller input.
Role: avoid a finite input search while retaining the exact delta-dependent gap. -/
theorem QNegOne_le_of_local_certificate {B : ℕ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {b x δ : ℝ}
    (hB : 10 ≤ Real.log B) (hx : 2 ≤ x) (cert : Analysis.GammaLocalBudgetCertificate x δ)
    (hb : 1 ≤ b) (hbx : b ≤ (99 / 40 : ℝ) * x)
    (hgap : δ - 3 / 4 ≤ LLS.gammaFactorFreeSeparation (Real.log B) b x) :
    (QNegOne B : ℝ) ≤ (99 / 40 : ℝ) * x := by
  apply
    QNegOne_cast_le_of_forall
      (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 99 / 40) (zero_le_one.trans cert.scale_ge_one))
  intro n hn
  have ha := NumberTheory.mem_admissibleFinset_iff.mp hn
  obtain ⟨q, hq, ho, hqb, hval⟩ :=
    exists_prime_neg_one_witness_of_local_certificate ha.odd ha.not_isSquare hGRH hB
      (Real.log_le_log (Nat.cast_pos.mpr ha.odd.pos) (Nat.cast_le.mpr ha.le)) hx cert hb hbx hgap
  exact
    (Nat.cast_le.mpr
          (NumberTheory.primeNegOneWitness_le n
            (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare ha.odd ha.not_isSquare)
            ⟨hq, ho, hval⟩)).trans
      hqb

/-- Input: GRH, an odd nonsquare input, x>=1936 and the displayed cutoff-1000 scalar conditions.
Claim: an odd-prime negative witness exists through 99x/40.
Proof: instantiate the certificate with delta=4393/5000 and the prefix lower bound 203/50.
Role: expose the lower finite-scale entrance with required gap 643/5000. -/
theorem exists_prime_neg_one_witness_of_checkpoint1000_scale1936 {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {L b x D : ℝ}
    (hL : 10 ≤ L) (hlog : Real.log n ≤ L) (hx : 1936 ≤ x) (hb : 1000 ≤ b)
    (hbx : b ≤ (99 / 40 : ℝ) * x) (hD : LLS.gammaScaleSignedDualBudget L x ≤ D)
    (hgap : 643 / 5000 ≤ LLS.gammaPrefixSeparation L x D (203 / 50)) :
    ∃ q : ℕ, q.Prime ∧ Odd q ∧ (q : ℝ) ≤ (99 / 40 : ℝ) * x ∧ jacobiSym n q = -1 := by
  have hs := LLS.gamma_checkpoint1000_separation_le hGRH.riemann hb hD
  apply
    exists_prime_neg_one_witness_of_local_certificate hn hns hGRH hL hlog (by linarith only [hx])
      (Analysis.gamma_local_certificate1936 hx) (by linarith only [hb]) hbx
  norm_num only
  exact hgap.trans hs

/-- Input: GRH, x>=1936 and the displayed common-endpoint cutoff-1000 margin.
Claim: the full negative-witness maximum is at most 99x/40.
Proof: use the complete local certificate and certified prefix margin.
Role: remove local and boundary-tail fields from the finite maximum criterion. -/
theorem QNegOne_le_of_checkpoint1000_scale1936 {B : ℕ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {b x D : ℝ}
    (hB : 10 ≤ Real.log B) (hx : 1936 ≤ x) (hb : 1000 ≤ b) (hbx : b ≤ (99 / 40 : ℝ) * x)
    (hD : LLS.gammaScaleSignedDualBudget (Real.log B) x ≤ D)
    (hgap : 643 / 5000 ≤ LLS.gammaPrefixSeparation (Real.log B) x D (203 / 50)) :
    (QNegOne B : ℝ) ≤ (99 / 40 : ℝ) * x := by
  have hs := LLS.gamma_checkpoint1000_separation_le hGRH.riemann hb hD
  apply
    QNegOne_le_of_local_certificate hGRH hB (by linarith only [hx])
      (Analysis.gamma_local_certificate1936 hx) (by linarith only [hb]) hbx
  norm_num only
  exact hgap.trans hs

/-- Input: the same common-endpoint conditions as for the negative maximum.
Claim: the full non-one maximum is at most 99x/40.
Proof: compare the two maxima. Role: share the finite-scale analytic entrance. -/
theorem QNeOne_le_of_checkpoint1000_scale1936 {B : ℕ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {b x D : ℝ}
    (hB : 10 ≤ Real.log B) (hx : 1936 ≤ x) (hb : 1000 ≤ b) (hbx : b ≤ (99 / 40 : ℝ) * x)
    (hD : LLS.gammaScaleSignedDualBudget (Real.log B) x ≤ D)
    (hgap : 643 / 5000 ≤ LLS.gammaPrefixSeparation (Real.log B) x D (203 / 50)) :
    (QNeOne B : ℝ) ≤ (99 / 40 : ℝ) * x := by
  exact
    (Nat.cast_le.mpr (QNeOne_le_QNegOne B)).trans
      (QNegOne_le_of_checkpoint1000_scale1936 hGRH hB hx hb hbx hD hgap)

end PseudoPrime.PseudoSquare
