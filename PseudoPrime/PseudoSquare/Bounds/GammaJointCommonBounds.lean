/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaJointCommonComparison
public import PseudoPrime.PseudoSquare.Bounds.GammaSignedVariationBounds

/-! # Jacobi witnesses retaining joint principal and common Euler costs -/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- Under GRH and odd nonsquare data, the nonnegative joint common margin yields
an odd negative Jacobi prime through 99x/40. Transfer absence to unit-prime
triviality and use the joint principal comparison without a separate series cap. -/
theorem exists_prime_neg_one_witness_of_joint_common_separation {n Q : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hQ : 20000 ≤ Q) (hnQ : 4 * n ≤ Q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x b : ℝ} (hx : 2 ≤ x)
    (hb : 1 ≤ b) (hbx : b ≤ (99 / 40 : ℝ) * x)
    (hgap :
      0 ≤
        LLS.gammaJointCommonSeparation Q (NumberTheory.complexQuadraticCharacter n hn) b x
          (541 / 50)) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ jacobiSym n p = -1 := by
  let : NeZero (4 * n) := ⟨Nat.mul_ne_zero (by norm_num only) hn.pos.ne'⟩
  have hp :=
    (NumberTheory.primitiveCharacter_even_iff (NumberTheory.complexQuadraticCharacter n hn)).mpr
      (NumberTheory.complexQuadraticCharacter_isEven n hn)
  have hCost := LLS.gamma_even_common_cost_lt_precise hGRH.riemann hp
  have hne := NumberTheory.complexQuadraticCharacter_ne_one_of_not_square n hn hns
  by_contra hnone
  have hsmall :
    ∀ p : ℕ,
      p.Prime →
        ¬p ∣ 4 * n →
        (p : ℝ) ≤ (99 / 40 : ℝ) * x → NumberTheory.complexQuadraticCharacter n hn p = 1 := by
    intro p hp hd hpb
    by_contra hv
    have hm := NumberTheory.primeNegOneWitness_mem_of_complexQuadraticCharacter_ne_one n hn hp hd hv
    exact hnone ⟨p, hm.1, hm.2.1, hpb, hm.2.2⟩
  exact
    LLS.gamma_prime_trivial_false_of_joint_common hQ hnQ
      (NumberTheory.complexQuadraticCharacter n hn)
      (NumberTheory.complexQuadraticCharacter_isQuadratic n hn) hne hGRH hx hb hbx hCost hgap hsmall

/-- For log n<=L, x>=4096 and admissible prefix, scalar margin at least 7/60
gives an odd negative prime through 99x/40 under GRH. Choose the common pole
level and transfer the factor-free margin to the actual joint comparison. -/
theorem exists_prime_neg_one_witness_of_joint_factor_free_separation {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {L b x : ℝ}
    (hL : 10 ≤ L) (hlog : Real.log n ≤ L) (hx : 4096 ≤ x) (hb : 1 ≤ b) (hbx : b ≤ (99 / 40 : ℝ) * x)
    (hgap : 7 / 60 ≤ LLS.gammaJointFactorFreeSeparation L b x) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ jacobiSym n p = -1 := by
  let Q := max 20000 (4 * n)
  have hQ : 20000 ≤ Q := le_max_left _ _
  have hnQ : 4 * n ≤ Q := le_max_right _ _
  have hlogQ := LLS.gamma_log_pole_level_le_of_common_endpoint hn hL hlog
  have hs := LLS.gammaJointFactorFreeSeparation_le_actual (Q := Q) (b := b) hn hns hlog hx hlogQ
  have hg :
    0 ≤
      LLS.gammaJointCommonSeparation Q (NumberTheory.complexQuadraticCharacter n hn) b x
        (541 / 50) := by
    linarith only [hs, hgap]
  exact
    exists_prime_neg_one_witness_of_joint_common_separation hn hns hQ hnQ hGRH
      (by linarith only [hx]) hb hbx hg

/-- Under the joint factor-free scalar hypotheses, the least negative odd-prime
Jacobi witness is at most 99x/40. Apply leastness to the constructed prime.
No input certificate or additional principal-series hypothesis remains. -/
theorem primeNegOneWitness_cast_le_of_joint_factor_free_separation {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {L b x : ℝ}
    (hL : 10 ≤ L) (hlog : Real.log n ≤ L) (hx : 4096 ≤ x) (hb : 1 ≤ b) (hbx : b ≤ (99 / 40 : ℝ) * x)
    (hgap : 7 / 60 ≤ LLS.gammaJointFactorFreeSeparation L b x)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ (99 / 40 : ℝ) * x := by
  obtain ⟨p, hp, ho, hpb, hv⟩ :=
    exists_prime_neg_one_witness_of_joint_factor_free_separation hn hns hGRH hL hlog hx hb hbx hgap
  exact (Nat.cast_le.mpr (NumberTheory.primeNegOneWitness_le n hw ⟨hp, ho, hv⟩)).trans hpb

/-- Under the joint factor-free criterion, an odd non-one prime exists through
99x/40. Use the negative witness, which is a stronger value conclusion.
This exports the analytic improvement to the non-one witness interface. -/
theorem exists_prime_ne_one_witness_of_joint_factor_free_separation {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {L b x : ℝ}
    (hL : 10 ≤ L) (hlog : Real.log n ≤ L) (hx : 4096 ≤ x) (hb : 1 ≤ b) (hbx : b ≤ (99 / 40 : ℝ) * x)
    (hgap : 7 / 60 ≤ LLS.gammaJointFactorFreeSeparation L b x) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ jacobiSym n p ≠ 1 := by
  obtain ⟨p, hp, ho, hpb, hv⟩ :=
    exists_prime_neg_one_witness_of_joint_factor_free_separation hn hns hGRH hL hlog hx hb hbx hgap
  refine ⟨p, hp, ho, hpb, ?_⟩
  rw [hv]
  norm_num only

/-- Under GRH, log B>=10 and admissible scale and prefix, a scalar margin at
least 7/60 bounds QNegOne(B) by 99x/40. Apply the common-endpoint least-witness
criterion to every admissible n<=B using monotonicity of the logarithm. -/
theorem QNegOne_le_of_joint_factor_free_separation {B : ℕ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {b x : ℝ} (hB : 10 ≤ Real.log B)
    (hx : 4096 ≤ x) (hb : 1 ≤ b) (hbx : b ≤ (99 / 40 : ℝ) * x)
    (hgap : 7 / 60 ≤ LLS.gammaJointFactorFreeSeparation (Real.log B) b x) :
    (QNegOne B : ℝ) ≤ (99 / 40 : ℝ) * x := by
  apply
    QNegOne_cast_le_of_forall
      (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 99 / 40) (by linarith only [hx]))
  intro n hn
  have ha := NumberTheory.mem_admissibleFinset_iff.mp hn
  exact
    primeNegOneWitness_cast_le_of_joint_factor_free_separation ha.odd ha.not_isSquare hGRH hB
      (Real.log_le_log (Nat.cast_pos.mpr ha.odd.pos) (Nat.cast_le.mpr ha.le)) hx hb hbx hgap
      (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare ha.odd ha.not_isSquare)

/-- Under the same common-endpoint scalar hypotheses, QNeOne(B)<=99x/40.
Use QNeOne<=QNegOne and the proved negative finite-maximum bound. -/
theorem QNeOne_le_of_joint_factor_free_separation {B : ℕ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {b x : ℝ} (hB : 10 ≤ Real.log B)
    (hx : 4096 ≤ x) (hb : 1 ≤ b) (hbx : b ≤ (99 / 40 : ℝ) * x)
    (hgap : 7 / 60 ≤ LLS.gammaJointFactorFreeSeparation (Real.log B) b x) :
    (QNeOne B : ℝ) ≤ (99 / 40 : ℝ) * x := by
  exact
    (Nat.cast_le.mpr (QNeOne_le_QNegOne B)).trans
      (QNegOne_le_of_joint_factor_free_separation hGRH hB hx hb hbx hgap)

end PseudoPrime.PseudoSquare
