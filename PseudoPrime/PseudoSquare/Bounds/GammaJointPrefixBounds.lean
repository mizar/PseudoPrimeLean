/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaJointPrefixComparison
public import PseudoPrime.PseudoSquare.Bounds.GammaPrincipalPairedBounds
public import PseudoPrime.NumberTheory.PrimitiveJacobiCharacter

/-! # Jacobi witnesses from arbitrary-scale joint prefix separation -/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- Input: GRH, odd nonsquare n, Q >= max(20000,4n), x >= 2 and 1 <= b <= 99x/40.
Assume the even joint-prefix separation margin is nonnegative.
Claim: an odd-prime negative Jacobi witness exists through 99x/40.
Proof: transfer witness absence to unit-prime triviality of the even quadratic character.
Role: use new finite-scale budget estimates without a prescribed logarithmic profile. -/
theorem exists_prime_neg_one_witness_of_joint_prefix_separation {n Q : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hQ : 20000 ≤ Q) (hnQ : 4 * n ≤ Q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x b : ℝ} (hx : 2 ≤ x)
    (hb : 1 ≤ b) (hbx : b ≤ (99 / 40 : ℝ) * x)
    (hgap :
      0 ≤
        LLS.gammaJointPrefixSeparation Q (NumberTheory.complexQuadraticCharacter n hn) b x
          (-3 / 2)) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ jacobiSym n p = -1 := by
  let : NeZero (4 * n) := ⟨Nat.mul_ne_zero (by norm_num only) hn.pos.ne'⟩
  have hp :=
    (NumberTheory.primitiveCharacter_even_iff (NumberTheory.complexQuadraticCharacter n hn)).mpr
      (NumberTheory.complexQuadraticCharacter_isEven n hn)
  have hA := AnalyticNumberTheory.DirichletLFunction.gammaResolvent_gammaFactor_0_le hp
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
    LLS.gamma_ramp_prime_trivial_false_joint_prefix hQ hnQ
      (NumberTheory.complexQuadraticCharacter n hn)
      (NumberTheory.complexQuadraticCharacter_isQuadratic n hn) hne hGRH hx hb hbx hA hgap hsmall

/-- Input: the same joint-prefix data, separation margin and nonempty witness set.
Claim: the least odd-prime negative witness is at most 99x/40.
Proof: minimize the witness supplied by the separation theorem.
Role: expose the arbitrary-scale comparison to least-witness consumers. -/
theorem primeNegOneWitness_cast_le_of_joint_prefix_separation {n Q : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hQ : 20000 ≤ Q) (hnQ : 4 * n ≤ Q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x b : ℝ} (hx : 2 ≤ x)
    (hb : 1 ≤ b) (hbx : b ≤ (99 / 40 : ℝ) * x)
    (hgap :
      0 ≤
        LLS.gammaJointPrefixSeparation Q (NumberTheory.complexQuadraticCharacter n hn) b x (-3 / 2))
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ (99 / 40 : ℝ) * x := by
  obtain ⟨p, hp, ho, hpb, hv⟩ :=
    exists_prime_neg_one_witness_of_joint_prefix_separation hn hns hQ hnQ hGRH hx hb hbx hgap
  exact (Nat.cast_le.mpr (NumberTheory.primeNegOneWitness_le n hw ⟨hp, ho, hv⟩)).trans hpb

/-- Input: the same joint-prefix data and separation margin.
Claim: an odd-prime non-one Jacobi witness exists through 99x/40.
Proof: the constructed negative value is different from one.
Role: connect the joint analytic criterion to the non-one witness interface. -/
theorem exists_prime_ne_one_witness_of_joint_prefix_separation {n Q : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hQ : 20000 ≤ Q) (hnQ : 4 * n ≤ Q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x b : ℝ} (hx : 2 ≤ x)
    (hb : 1 ≤ b) (hbx : b ≤ (99 / 40 : ℝ) * x)
    (hgap :
      0 ≤
        LLS.gammaJointPrefixSeparation Q (NumberTheory.complexQuadraticCharacter n hn) b x
          (-3 / 2)) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ jacobiSym n p ≠ 1 := by
  obtain ⟨p, hp, ho, hpb, hv⟩ :=
    exists_prime_neg_one_witness_of_joint_prefix_separation hn hns hQ hnQ hGRH hx hb hbx hgap
  refine ⟨p, hp, ho, hpb, ?_⟩
  rw [hv]
  norm_num only

end PseudoPrime.PseudoSquare
