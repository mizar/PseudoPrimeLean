/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.FamilyWeightedReindex

/-! # Gap-weighted actual zero sums for finite character families -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

namespace LogFreeDensity

open Classical in
/-- Positive absolute constants bound the actual divisor-weighted near-one zero
sum of any finite character family outside the reduced exceptional conductors,
with conductor four excluded. The real-part and scale conditions are explicit.
Select the family packet in the occurrence ledger and apply the proved gap-weighted
density estimate, then reindex exactly by character labels. No extra character-count
factor, unproved density input, or RH assumption is introduced. -/
theorem exists_character_family_weighted_zero_sum_off_exceptional_conductors :
    ∃ A C : ℝ,
      0 < A ∧
        0 < C ∧
        ∀ (c : ℝ),
          0 < c →
            ∀ (R : ℕ),
              2 ≤ R →
                ∀ (x σ₀ : ℝ),
                  1 < x →
                    (1 / 2 : ℝ) ≤ σ₀ →
                    σ₀ ≤ 1 →
                    A * (1 - σ₀) ≤ 1 / 2 →
                    2 * A * Real.log ((R + 1 : ℕ) : ℝ) ≤ Real.log x →
                    ∀ S : Finset (FamilyCharacterLabel R),
                      (∀ p ∈ S, p.1.val + 1 ≠ 4) →
                        (∀ p ∈ S,
                          p.1.val + 1 ∉
                            exceptionalFamilyConductorsAwayFromFour R (1 - c / Real.log R)) →
                        (∑ p ∈ S,
                            if hne : p.2 ≠ 1 then
                              if _hp : p.2.IsPrimitive then
                                ∑
                                  ρ ∈
                                    completedZerosInRectangle p.2 hne
                                      ((σ₀ : ℂ) - (R : ℝ) * Complex.I)
                                      ((1 : ℂ) + (R : ℝ) * Complex.I),
                                  (MeromorphicOn.divisor p.2.completedLFunction Set.univ ρ : ℝ) *
                                    (x ^ ρ.re / (1 + ρ.im ^ 2))
                              else 0
                            else 0) ≤
                          C * x * Real.exp (-(c / Real.log R) * Real.log x / 2) := by
  obtain ⟨A, C, hA, hC, hbound⟩ :=
    exists_family_rpow_inverse_quadratic_sum_off_exceptional_conductors
  refine ⟨A, C, hA, hC, ?_⟩
  intro c hc R hR x σ₀ hx hσlo hσhi hδ hscale S hfour havoid
  let T :=
    (primitiveCharacterFamilyZeroOccurrenceLedger R σ₀ R).filter
      (fun o ↦ familyZeroOccurrenceCharacterLabel o ∈ S)
  have hT : T ⊆ primitiveCharacterFamilyZeroOccurrenceLedger R (1 / 2) R := fun o ho ↦
    familyZeroOccurrence_ledger_mono_realpart hσlo hσhi (Finset.mem_filter.mp ho).1
  have hb :=
    hbound c hc R hR x σ₀ hx hσlo hσhi hδ hscale T hT
      (fun o ho ↦ (familyZeroOccurrence_realpart_bounds hσhi (Finset.mem_filter.mp ho).1).1)
      (fun o ho ↦ hfour (familyZeroOccurrenceCharacterLabel o) (Finset.mem_filter.mp ho).2)
      (fun o ho ↦ havoid (familyZeroOccurrenceCharacterLabel o) (Finset.mem_filter.mp ho).2)
  dsimp only [T] at hb
  rw [sum_familyZeroOccurrence_filter_labels_eq R R σ₀ S
      (fun ρ : ℂ ↦ x ^ ρ.re / (1 + ρ.im ^ 2))] at hb
  exact hb

end LogFreeDensity

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
