/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaPrincipalCapComparison
public import PseudoPrime.LLS.GammaRetainedCommonCostBounds
public import PseudoPrime.PseudoSquare.Bounds.GammaJointPrefixBounds

/-! # Jacobi witness criteria using the sharper principal Gamma upper bound -/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- Input: GRH, odd nonsquare n, ambient level and admissible scale and prefix.
A nonnegative joint margin using the signed-variation principal cap gives an
odd-prime negative Jacobi witness through 99x/40. Transfer absence to the even
quadratic character. Role: connect the improved principal error to witness extraction. -/
theorem exists_prime_neg_one_witness_of_signed_principal_separation {n Q : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hQ : 20000 ≤ Q) (hnQ : 4 * n ≤ Q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x b : ℝ} (hx : 2 ≤ x)
    (hb : 1 ≤ b) (hbx : b ≤ (99 / 40 : ℝ) * x)
    (hgap :
      0 ≤
        LLS.gammaJointPrefixSeparationWithPrincipalCap Q
          (NumberTheory.complexQuadraticCharacter n hn) b x (-3 / 2)
          (LLS.gammaSignedVariationPrincipalCap x)) :
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
    LLS.gamma_ramp_prime_trivial_false_of_principal_cap hQ hnQ
      (NumberTheory.complexQuadraticCharacter n hn)
      (NumberTheory.complexQuadraticCharacter_isQuadratic n hn) hne hGRH hx hb hbx hA
      (LLS.gamma_level_one_sum_le_signed_variation_cap hGRH.riemann
        ((by norm_num only : (1 : ℝ) ≤ 2).trans hx))
      hgap hsmall

/-- Under the same analytic and arithmetic conditions and a nonempty witness
set, the least negative odd-prime witness is at most 99x/40. Compare it with
the constructed witness. Role: expose minimality over all odd-prime witnesses. -/
theorem primeNegOneWitness_cast_le_of_signed_principal_separation {n Q : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hQ : 20000 ≤ Q) (hnQ : 4 * n ≤ Q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x b : ℝ} (hx : 2 ≤ x)
    (hb : 1 ≤ b) (hbx : b ≤ (99 / 40 : ℝ) * x)
    (hgap :
      0 ≤
        LLS.gammaJointPrefixSeparationWithPrincipalCap Q
          (NumberTheory.complexQuadraticCharacter n hn) b x (-3 / 2)
          (LLS.gammaSignedVariationPrincipalCap x))
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ (99 / 40 : ℝ) * x := by
  obtain ⟨p, hp, ho, hpb, hv⟩ :=
    exists_prime_neg_one_witness_of_signed_principal_separation hn hns hQ hnQ hGRH hx hb hbx hgap
  exact (Nat.cast_le.mpr (NumberTheory.primeNegOneWitness_le n hw ⟨hp, ho, hv⟩)).trans hpb

/-- Under the same signed-principal margin, a non-one odd-prime Jacobi witness
exists through 99x/40. Use the negative witness. Role: export the improved
principal subtraction to both quadratic witness predicates. -/
theorem exists_prime_ne_one_witness_of_signed_principal_separation {n Q : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hQ : 20000 ≤ Q) (hnQ : 4 * n ≤ Q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x b : ℝ} (hx : 2 ≤ x)
    (hb : 1 ≤ b) (hbx : b ≤ (99 / 40 : ℝ) * x)
    (hgap :
      0 ≤
        LLS.gammaJointPrefixSeparationWithPrincipalCap Q
          (NumberTheory.complexQuadraticCharacter n hn) b x (-3 / 2)
          (LLS.gammaSignedVariationPrincipalCap x)) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ jacobiSym n p ≠ 1 := by
  obtain ⟨p, hp, ho, hpb, hv⟩ :=
    exists_prime_neg_one_witness_of_signed_principal_separation hn hns hQ hnQ hGRH hx hb hbx hgap
  refine ⟨p, hp, ho, hpb, ?_⟩
  rw [hv]
  norm_num only

/-- Under GRH and the displayed odd-nonsquare and scale conditions, the joint
margin with common cost 541/50 gives the stated negative or non-one witness bound.
Use evenness and the precise common cost, then the principal-cap comparison.
Role: export the improved fixed cost to pointwise and least witnesses. -/
theorem exists_prime_neg_one_witness_of_retained_common_separation {n Q : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hQ : 20000 ≤ Q) (hnQ : 4 * n ≤ Q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x b : ℝ} (hx : 2 ≤ x)
    (hb : 1 ≤ b) (hbx : b ≤ (99 / 40 : ℝ) * x)
    (hgap :
      0 ≤
        LLS.gammaJointPrefixSeparationWithCommonCap Q (NumberTheory.complexQuadraticCharacter n hn)
          b x (541 / 50) (LLS.gammaSignedVariationPrincipalCap x)) :
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
    LLS.gamma_ramp_prime_trivial_false_of_common_cap hQ hnQ
      (NumberTheory.complexQuadraticCharacter n hn)
      (NumberTheory.complexQuadraticCharacter_isQuadratic n hn) hne hGRH hx hb hbx hCost
      (LLS.gamma_level_one_sum_le_signed_variation_cap hGRH.riemann
        ((by norm_num only : (1 : ℝ) ≤ 2).trans hx))
      hgap hsmall

/-- Under GRH and the displayed odd-nonsquare and scale conditions, the joint
margin with common cost 541/50 gives the stated negative or non-one witness bound.
Use evenness and the precise common cost, then the principal-cap comparison.
Role: export the improved fixed cost to pointwise and least witnesses. -/
theorem primeNegOneWitness_cast_le_of_retained_common_separation {n Q : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hQ : 20000 ≤ Q) (hnQ : 4 * n ≤ Q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x b : ℝ} (hx : 2 ≤ x)
    (hb : 1 ≤ b) (hbx : b ≤ (99 / 40 : ℝ) * x)
    (hgap :
      0 ≤
        LLS.gammaJointPrefixSeparationWithCommonCap Q (NumberTheory.complexQuadraticCharacter n hn)
          b x (541 / 50) (LLS.gammaSignedVariationPrincipalCap x))
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ (99 / 40 : ℝ) * x := by
  obtain ⟨p, hp, ho, hpb, hv⟩ :=
    exists_prime_neg_one_witness_of_retained_common_separation hn hns hQ hnQ hGRH hx hb hbx hgap
  exact (Nat.cast_le.mpr (NumberTheory.primeNegOneWitness_le n hw ⟨hp, ho, hv⟩)).trans hpb

/-- Under GRH and the displayed odd-nonsquare and scale conditions, the joint
margin with common cost 541/50 gives the stated negative or non-one witness bound.
Use evenness and the precise common cost, then the principal-cap comparison.
Role: export the improved fixed cost to pointwise and least witnesses. -/
theorem exists_prime_ne_one_witness_of_retained_common_separation {n Q : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hQ : 20000 ≤ Q) (hnQ : 4 * n ≤ Q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x b : ℝ} (hx : 2 ≤ x)
    (hb : 1 ≤ b) (hbx : b ≤ (99 / 40 : ℝ) * x)
    (hgap :
      0 ≤
        LLS.gammaJointPrefixSeparationWithCommonCap Q (NumberTheory.complexQuadraticCharacter n hn)
          b x (541 / 50) (LLS.gammaSignedVariationPrincipalCap x)) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ jacobiSym n p ≠ 1 := by
  obtain ⟨p, hp, ho, hpb, hv⟩ :=
    exists_prime_neg_one_witness_of_retained_common_separation hn hns hQ hnQ hGRH hx hb hbx hgap
  refine ⟨p, hp, ho, hpb, ?_⟩
  rw [hv]
  norm_num only

/-- Under the displayed GRH, arithmetic and scale conditions, a factor-free margin
of at least 7/60 after adding 9/50 gives the stated witness or maximum bound.
Apply the retained common-cost comparison, then minimize or maximize.
Role: use the common saving without new input or prime-power certificates. -/
theorem exists_prime_neg_one_witness_of_retained_common_factor_free_separation {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {L b x : ℝ}
    (hL : 10 ≤ L) (hlog : Real.log n ≤ L) (hx : 4096 ≤ x) (hb : 1 ≤ b) (hbx : b ≤ (99 / 40 : ℝ) * x)
    (hgap : 7 / 60 ≤ LLS.gammaSignedPrincipalFactorFreeSeparation L b x + 9 / 50) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ jacobiSym n p = -1 := by
  let Q := max 20000 (4 * n)
  have hQ : 20000 ≤ Q := le_max_left _ _
  have hnQ : 4 * n ≤ Q := le_max_right _ _
  have hlogQ := LLS.gamma_log_pole_level_le_of_common_endpoint hn hL hlog
  have hs := LLS.gamma_retained_common_factor_free_le_joint (Q := Q) (b := b) hn hns hlog hx hlogQ
  have hg :
    0 ≤
      LLS.gammaJointPrefixSeparationWithCommonCap Q (NumberTheory.complexQuadraticCharacter n hn) b
        x (541 / 50) (LLS.gammaSignedVariationPrincipalCap x) := by
    linarith only [hs, hgap]
  exact
    exists_prime_neg_one_witness_of_retained_common_separation hn hns hQ hnQ hGRH
      (by linarith only [hx]) hb hbx hg

/-- Under the displayed GRH, arithmetic and scale conditions, a factor-free margin
of at least 7/60 after adding 9/50 gives the stated witness or maximum bound.
Apply the retained common-cost comparison, then minimize or maximize.
Role: use the common saving without new input or prime-power certificates. -/
theorem primeNegOneWitness_cast_le_of_retained_common_factor_free_separation {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {L b x : ℝ}
    (hL : 10 ≤ L) (hlog : Real.log n ≤ L) (hx : 4096 ≤ x) (hb : 1 ≤ b) (hbx : b ≤ (99 / 40 : ℝ) * x)
    (hgap : 7 / 60 ≤ LLS.gammaSignedPrincipalFactorFreeSeparation L b x + 9 / 50)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ (99 / 40 : ℝ) * x := by
  obtain ⟨p, hp, ho, hpb, hv⟩ :=
    exists_prime_neg_one_witness_of_retained_common_factor_free_separation hn hns hGRH hL hlog hx hb
      hbx hgap
  exact (Nat.cast_le.mpr (NumberTheory.primeNegOneWitness_le n hw ⟨hp, ho, hv⟩)).trans hpb

/-- Under the displayed GRH, arithmetic and scale conditions, a factor-free margin
of at least 7/60 after adding 9/50 gives the stated witness or maximum bound.
Apply the retained common-cost comparison, then minimize or maximize.
Role: use the common saving without new input or prime-power certificates. -/
theorem exists_prime_ne_one_witness_of_retained_common_factor_free_separation {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {L b x : ℝ}
    (hL : 10 ≤ L) (hlog : Real.log n ≤ L) (hx : 4096 ≤ x) (hb : 1 ≤ b) (hbx : b ≤ (99 / 40 : ℝ) * x)
    (hgap : 7 / 60 ≤ LLS.gammaSignedPrincipalFactorFreeSeparation L b x + 9 / 50) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ jacobiSym n p ≠ 1 := by
  obtain ⟨p, hp, ho, hpb, hv⟩ :=
    exists_prime_neg_one_witness_of_retained_common_factor_free_separation hn hns hGRH hL hlog hx hb
      hbx hgap
  refine ⟨p, hp, ho, hpb, ?_⟩
  rw [hv]
  norm_num only

/-- Under the displayed GRH, arithmetic and scale conditions, a factor-free margin
of at least 7/60 after adding 9/50 gives the stated witness or maximum bound.
Apply the retained common-cost comparison, then minimize or maximize.
Role: use the common saving without new input or prime-power certificates. -/
theorem QNegOne_le_of_retained_common_factor_free_separation {B : ℕ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {b x : ℝ} (hB : 10 ≤ Real.log B)
    (hx : 4096 ≤ x) (hb : 1 ≤ b) (hbx : b ≤ (99 / 40 : ℝ) * x)
    (hgap : 7 / 60 ≤ LLS.gammaSignedPrincipalFactorFreeSeparation (Real.log B) b x + 9 / 50) :
    (QNegOne B : ℝ) ≤ (99 / 40 : ℝ) * x := by
  apply
    QNegOne_cast_le_of_forall
      (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 99 / 40) (by linarith only [hx]))
  intro n hn
  have ha := NumberTheory.mem_admissibleFinset_iff.mp hn
  exact
    primeNegOneWitness_cast_le_of_retained_common_factor_free_separation ha.odd ha.not_isSquare hGRH
      hB (Real.log_le_log (Nat.cast_pos.mpr ha.odd.pos) (Nat.cast_le.mpr ha.le)) hx hb hbx hgap
      (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare ha.odd ha.not_isSquare)

/-- Under the displayed GRH, arithmetic and scale conditions, a factor-free margin
of at least 7/60 after adding 9/50 gives the stated witness or maximum bound.
Apply the retained common-cost comparison, then minimize or maximize.
Role: use the common saving without new input or prime-power certificates. -/
theorem QNeOne_le_of_retained_common_factor_free_separation {B : ℕ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {b x : ℝ} (hB : 10 ≤ Real.log B)
    (hx : 4096 ≤ x) (hb : 1 ≤ b) (hbx : b ≤ (99 / 40 : ℝ) * x)
    (hgap : 7 / 60 ≤ LLS.gammaSignedPrincipalFactorFreeSeparation (Real.log B) b x + 9 / 50) :
    (QNeOne B : ℝ) ≤ (99 / 40 : ℝ) * x := by
  exact
    (Nat.cast_le.mpr (QNeOne_le_QNegOne B)).trans
      (QNegOne_le_of_retained_common_factor_free_separation hGRH hB hx hb hbx hgap)

end PseudoPrime.PseudoSquare
