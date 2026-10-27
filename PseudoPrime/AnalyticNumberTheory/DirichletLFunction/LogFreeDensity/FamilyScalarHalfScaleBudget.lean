/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.HalfScaleBudgetMonotonicity
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.FamilyFullHalfScaleBudget
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.CharacterFamilyCardinality

/-! # Scalar modulus majorants for the full half-scale family budget -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

open Classical in
/-- For a finite character family at bounded nonzero level and scale at least two,
nonnegative budget constants bound the primitive remainder sum by the level times
one remainder at that level. Each primitive conductor is smaller, and the image
has cardinality at most the original level. This removes dependent labels from
the remainder that must be absorbed uniformly. -/
theorem sum_primitive_remainders_le_level_budget {q Q H : ℕ} [NeZero q] (hq : q ≤ Q)
    (S : Finset (DirichletCharacter ℂ q)) {x σ C K T : ℝ} (hx : 2 ≤ x) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hT : 0 ≤ T) :
    (∑ p ∈ S.image (Arithmetic.boundedPrimitiveCharacterLabel hq),
        primitiveHalfScaleRemainderBudget (p.1.val + 1) x σ H C K T) ≤
      (q : ℝ) * primitiveHalfScaleRemainderBudget q x σ H C K T := by
  have hs :
    (∑ p ∈ S.image (Arithmetic.boundedPrimitiveCharacterLabel hq),
        primitiveHalfScaleRemainderBudget (p.1.val + 1) x σ H C K T) ≤
      ∑ _p ∈ S.image (Arithmetic.boundedPrimitiveCharacterLabel hq),
        primitiveHalfScaleRemainderBudget q x σ H C K T := by
    apply Finset.sum_le_sum
    intro p hp
    obtain ⟨χ, hχ, rfl⟩ := Finset.mem_image.mp hp
    exact
      primitiveHalfScaleRemainderBudget_mono_modulus (Nat.succ_pos _)
        (Arithmetic.boundedPrimitiveCharacterLabel_level_le hq χ) hx hK hT
  rw [Finset.sum_const, nsmul_eq_mul] at hs
  have hcard : (((S.image (Arithmetic.boundedPrimitiveCharacterLabel hq)).card : ℕ) : ℝ) ≤ q := by
    exact_mod_cast Finset.card_image_le.trans (Arithmetic.card_character_family_le_level S)
  exact
    hs.trans
      (mul_le_mul_of_nonneg_right hcard
        (primitiveHalfScaleRemainderBudget_nonneg (NeZero.pos q) hx hC hK hT))

/-- At any real scale and nonzero level, the explicit family level-change
correction is at most `q^2 log(x)^2`. Bound both the family size and the distinct
prime-factor count by the level. This coarse scalar estimate suffices for
polynomial-height scale selection. -/
theorem character_level_correction_le_square {q : ℕ} [NeZero q]
    (S : Finset (DirichletCharacter ℂ q)) (x : ℝ) :
    (S.card : ℝ) * ((q.primeFactors.card : ℝ) * (Real.log x) ^ 2) ≤
      (q : ℝ) ^ 2 * (Real.log x) ^ 2 := by
  have hs : (S.card : ℝ) ≤ q := by exact_mod_cast Arithmetic.card_character_family_le_level S
  have hω : (q.primeFactors.card : ℝ) ≤ q := by
    exact_mod_cast Arithmetic.card_primeFactors_le_level (NeZero.ne q)
  have hm := mul_le_mul hs hω (Nat.cast_nonneg q.primeFactors.card) (Nat.cast_nonneg q)
  have hmul := mul_le_mul_of_nonneg_right hm (sq_nonneg (Real.log x))
  nlinarith only [hmul]

namespace LogFreeDensity

open Classical in
/-- Fixed positive constants give a scalar half-scale bound for every finite
nonprincipal family avoiding exceptional conductor divisors, including conductor
four. Preserve the leading gap-controlled and arbitrary-precision errors, bound
the primitive remainder sum by one level majorant, and bound the level correction
quadratically. The remaining expression depends only on the level and the chosen
scale parameters, so its uniform absorption is a scalar analytic problem. -/
theorem exists_character_family_scalar_half_scale_budget :
    ∃ A B C K T : ℝ,
      0 < A ∧
        0 < B ∧
        0 < C ∧
        0 < K ∧
        0 < T ∧
        ∀ (ε : ℝ),
          0 < ε →
            ∃ X : ℝ,
              4 ≤ X ∧
                ∀ (c : ℝ),
                  0 < c →
                    ∀ (H : ℕ),
                      2 ≤ H →
                        ∀ (x σ : ℝ),
                          X ≤ x →
                            (1 / 2 : ℝ) ≤ σ →
                            σ ≤ 1 →
                            A * (1 - σ) ≤ 1 / 2 →
                            2 * A * Real.log ((H + 1 + 1 : ℕ) : ℝ) ≤ Real.log x →
                            ∀ (q : ℕ) [NeZero q],
                              q ≤ H + 1 →
                                ∀ S : Finset (DirichletCharacter ℂ q),
                                  (∀ χ ∈ S, χ ≠ 1) →
                                    (∀
                                      e ∈
                                        exceptionalFamilyConductorsAwayFromFour (H + 1)
                                          (1 - c / Real.log ((H + 1 : ℕ) : ℝ)),
                                      ¬e ∣ q) →
                                    (∑ χ ∈ S,
                                        ‖Arithmetic.characterLogWeightedSum x χ -
                                            Arithmetic.characterLogWeightedSum (x / 2) χ‖) ≤
                                      B * x *
                                          Real.exp
                                            (-(c / Real.log ((H + 1 : ℕ) : ℝ)) * Real.log x / 2) +
                                        ε * x +
                                        (q : ℝ) * primitiveHalfScaleRemainderBudget q x σ H C K T +
                                        (q : ℝ) ^ 2 * (Real.log x) ^ 2 := by
  obtain ⟨A, B, C, K, T, hA, hB, hC, hK, hT, hbudget⟩ := exists_character_family_half_scale_budget
  refine ⟨A, B, C, K, T, hA, hB, hC, hK, hT, ?_⟩
  intro ε hε
  obtain ⟨X, hX, hbound⟩ := hbudget ε hε
  refine ⟨X, hX, ?_⟩
  intro c hc H hH x σ hx hσlo hσhi hδ hscale q inst hq S hne havoid
  have hb := hbound c hc H hH x σ hx hσlo hσhi hδ hscale q hq S hne havoid
  have hr :=
    sum_primitive_remainders_le_level_budget (H := H) (σ := σ) hq
      (S.filter (fun χ ↦ χ.conductor ≠ 4)) (by linarith only [hX.trans hx] : 2 ≤ x) hC.le hK.le
      hT.le
  have he := character_level_correction_le_square S x
  exact hb.trans (add_le_add (add_le_add le_rfl hr) he)

end LogFreeDensity

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
