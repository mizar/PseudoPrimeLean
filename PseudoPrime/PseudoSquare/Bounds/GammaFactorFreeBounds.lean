/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PseudoSquare.Bounds.GammaJointPrefixBounds
public import PseudoPrime.LLS.GammaScaleJointBudget

/-! # Quadratic witnesses from a factor-independent scalar separation -/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- Input: GRH, odd nonsquare n, L >= 10, log n <= L, x >= 4096 and 1 <= b <= 99x/40.
Assume the factor-independent scalar margin is at least 7/60.
Claim: an odd-prime negative witness exists through 99x/40.
Proof: choose an auxiliary pole level and transfer the scalar margin to the actual character.
Role: remove factorization and conductor data from the witness criterion. -/
theorem exists_prime_neg_one_witness_of_factor_free_separation {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {L b x : ℝ}
    (hL : 10 ≤ L) (hlog : Real.log n ≤ L) (hx : 4096 ≤ x) (hb : 1 ≤ b) (hbx : b ≤ (99 / 40 : ℝ) * x)
    (hgap : 7 / 60 ≤ LLS.gammaFactorFreeSeparation L b x) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ jacobiSym n p = -1 := by
  let Q := max 20000 (4 * n)
  have hQ : 20000 ≤ Q := le_max_left _ _
  have hnQ : 4 * n ≤ Q := le_max_right _ _
  have hlogQ := LLS.gamma_log_pole_level_le_of_common_endpoint hn hL hlog
  have hs :=
    LLS.gamma_factor_free_separation_le_joint_add_small_scale (Q := Q) (b := b) hn hns hlog hx hlogQ
  have hg :
    0 ≤
      LLS.gammaJointPrefixSeparation Q (NumberTheory.complexQuadraticCharacter n hn) b x
        (-3 / 2) := by
    linarith only [hs, hgap]
  exact
    exists_prime_neg_one_witness_of_joint_prefix_separation hn hns hQ hnQ hGRH
      (by linarith only [hx]) hb hbx hg

/-- Input: the same scalar conditions and a nonempty least-negative-witness set.
Claim: the least odd-prime negative witness is at most 99x/40.
Proof: minimize the witness obtained from the factor-independent separation.
Role: provide a common endpoint estimate for arbitrary admissible inputs. -/
theorem primeNegOneWitness_cast_le_of_factor_free_separation {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {L b x : ℝ}
    (hL : 10 ≤ L) (hlog : Real.log n ≤ L) (hx : 4096 ≤ x) (hb : 1 ≤ b) (hbx : b ≤ (99 / 40 : ℝ) * x)
    (hgap : 7 / 60 ≤ LLS.gammaFactorFreeSeparation L b x)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ (99 / 40 : ℝ) * x := by
  obtain ⟨p, hp, ho, hpb, hv⟩ :=
    exists_prime_neg_one_witness_of_factor_free_separation hn hns hGRH hL hlog hx hb hbx hgap
  exact (Nat.cast_le.mpr (NumberTheory.primeNegOneWitness_le n hw ⟨hp, ho, hv⟩)).trans hpb

/-- Input: the same scalar conditions under GRH.
Claim: an odd-prime non-one witness exists through 99x/40.
Proof: the negative witness has value different from one.
Role: connect the scalar comparison to the non-one witness interface. -/
theorem exists_prime_ne_one_witness_of_factor_free_separation {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {L b x : ℝ}
    (hL : 10 ≤ L) (hlog : Real.log n ≤ L) (hx : 4096 ≤ x) (hb : 1 ≤ b) (hbx : b ≤ (99 / 40 : ℝ) * x)
    (hgap : 7 / 60 ≤ LLS.gammaFactorFreeSeparation L b x) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ jacobiSym n p ≠ 1 := by
  obtain ⟨p, hp, ho, hpb, hv⟩ :=
    exists_prime_neg_one_witness_of_factor_free_separation hn hns hGRH hL hlog hx hb hbx hgap
  refine ⟨p, hp, ho, hpb, ?_⟩
  rw [hv]
  norm_num only

/-- Input: GRH, log B >= 10, x >= 4096, a valid prefix and scalar margin at least 7/60.
Claim: the full finite maximum of least negative witnesses through B is at most 99x/40.
Proof: use the common endpoint for every admissible n <= B, including small n.
Role: avoid finite input enumeration when a scalar interval estimate is supplied. -/
theorem QNegOne_le_of_factor_free_separation {B : ℕ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {b x : ℝ} (hB : 10 ≤ Real.log B)
    (hx : 4096 ≤ x) (hb : 1 ≤ b) (hbx : b ≤ (99 / 40 : ℝ) * x)
    (hgap : 7 / 60 ≤ LLS.gammaFactorFreeSeparation (Real.log B) b x) :
    (QNegOne B : ℝ) ≤ (99 / 40 : ℝ) * x := by
  apply
    QNegOne_cast_le_of_forall
      (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 99 / 40) (by linarith only [hx]))
  intro n hn
  have ha := NumberTheory.mem_admissibleFinset_iff.mp hn
  exact
    primeNegOneWitness_cast_le_of_factor_free_separation ha.odd ha.not_isSquare hGRH hB
      (Real.log_le_log (Nat.cast_pos.mpr ha.odd.pos) (Nat.cast_le.mpr ha.le)) hx hb hbx hgap
      (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare ha.odd ha.not_isSquare)

/-- Input: the same scalar conditions for the endpoint B.
Claim: the full non-one witness maximum is at most 99x/40.
Proof: compare it to the negative witness maximum.
Role: extend the factor-independent certificate to both quadratic witness maxima. -/
theorem QNeOne_le_of_factor_free_separation {B : ℕ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {b x : ℝ} (hB : 10 ≤ Real.log B)
    (hx : 4096 ≤ x) (hb : 1 ≤ b) (hbx : b ≤ (99 / 40 : ℝ) * x)
    (hgap : 7 / 60 ≤ LLS.gammaFactorFreeSeparation (Real.log B) b x) :
    (QNeOne B : ℝ) ≤ (99 / 40 : ℝ) * x := by
  exact
    (Nat.cast_le.mpr (QNeOne_le_QNegOne B)).trans
      (QNegOne_le_of_factor_free_separation hGRH hB hx hb hbx hgap)

end PseudoPrime.PseudoSquare
