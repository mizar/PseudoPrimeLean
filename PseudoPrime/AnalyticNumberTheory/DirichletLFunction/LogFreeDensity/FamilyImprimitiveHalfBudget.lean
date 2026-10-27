/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.FamilyHalfScaleBudget
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimitiveHalfScaleTransfer

/-! # General character families outside exceptional primitive conductors -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity

open Classical in
/-- Fixed positive constants bound the half-scale norm sum of any finite
nonprincipal family at a nonzero level below the height scale, excluding primitive
conductor four and all exceptional conductor divisors of that level. Transfer to
injectively bounded primitive labels, apply the unconditional primitive-family
budget, and add the explicit level-change correction. The leading exponential
error has no character-count factor. Conductor four and absorption of the displayed
remainders are separate remaining steps in the uniform theta-supply argument. -/
theorem exists_character_family_half_scale_budget_off_exceptional_conductors :
    ∃ A B C K T : ℝ,
      0 < A ∧
        0 < B ∧
        0 < C ∧
        0 < K ∧
        0 < T ∧
        ∀ (c : ℝ),
          0 < c →
            ∀ (H : ℕ),
              2 ≤ H →
                ∀ (x σ : ℝ),
                  4 ≤ x →
                    (1 / 2 : ℝ) ≤ σ →
                    σ ≤ 1 →
                    A * (1 - σ) ≤ 1 / 2 →
                    2 * A * Real.log ((H + 1 + 1 : ℕ) : ℝ) ≤ Real.log x →
                    ∀ (q : ℕ) [NeZero q] (hq : q ≤ H + 1),
                      ∀ S : Finset (DirichletCharacter ℂ q),
                        (∀ χ ∈ S, χ ≠ 1) →
                          (∀ χ ∈ S, χ.conductor ≠ 4) →
                          (∀
                            e ∈
                              exceptionalFamilyConductorsAwayFromFour (H + 1)
                                (1 - c / Real.log ((H + 1 : ℕ) : ℝ)),
                            ¬e ∣ q) →
                          (∑ χ ∈ S,
                              ‖Arithmetic.characterLogWeightedSum x χ -
                                  Arithmetic.characterLogWeightedSum (x / 2) χ‖) ≤
                            B * x * Real.exp (-(c / Real.log ((H + 1 : ℕ) : ℝ)) * Real.log x / 2) +
                              (∑ p ∈ S.image (Arithmetic.boundedPrimitiveCharacterLabel hq),
                                primitiveHalfScaleRemainderBudget (p.1.val + 1) x σ H C K T) +
                              (S.card : ℝ) * ((q.primeFactors.card : ℝ) * (Real.log x) ^ 2) := by
  obtain ⟨A, B, C, K, T, hA, hB, hC, hK, hT, hbudget⟩ :=
    exists_primitive_character_family_half_scale_budget_off_exceptional_conductors
  refine ⟨A, B, C, K, T, hA, hB, hC, hK, hT, ?_⟩
  intro c hc H hH x σ hx hσlo hσhi hδ hscale q inst hq S hne hfour havoid
  let F := Arithmetic.boundedPrimitiveCharacterLabel hq
  let P := S.image F
  have hprops (p : FamilyCharacterLabel (H + 1)) (hp : p ∈ P) :
    p.2.IsPrimitive ∧
      p.2 ≠ 1 ∧
      p.1.val + 1 ≠ 4 ∧
      p.1.val + 1 ∉
        exceptionalFamilyConductorsAwayFromFour (H + 1) (1 - c / Real.log ((H + 1 : ℕ) : ℝ)) := by
    obtain ⟨χ, hχ, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨he, hprim, hn⟩ := Arithmetic.boundedPrimitiveCharacterLabel_properties hq χ (hne χ hχ)
    refine ⟨hprim, hn, ?_, ?_⟩
    · change (Arithmetic.boundedPrimitiveCharacterLabel hq χ).1.val + 1 ≠ 4
      rw [he]
      exact hfour χ hχ
    · change (Arithmetic.boundedPrimitiveCharacterLabel hq χ).1.val + 1 ∉ _
      rw [he]
      exact fun hm ↦ havoid χ.conductor hm χ.conductor_dvd_level
  have hb :=
    hbudget c hc H hH x σ hx hσlo hσhi hδ hscale P (fun p hp ↦ (hprops p hp).1)
      (fun p hp ↦ (hprops p hp).2.1) (fun p hp ↦ (hprops p hp).2.2.1)
      (fun p hp ↦ (hprops p hp).2.2.2)
  have ht :=
    Arithmetic.sum_norm_characterLogWeightedSum_half_le_bounded_primitive_labels hq S
      (by linarith only [hx] : 2 ≤ x)
  exact ht.trans (add_le_add hb le_rfl)

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity
