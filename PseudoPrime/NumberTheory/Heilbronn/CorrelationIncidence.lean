/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.FiniteCorrelationAmplification
public import PseudoPrime.NumberTheory.Heilbronn.CorrelationLevels

/-! # Incidence representations of Heilbronn difference correlations -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- Finite-set presentation of the zero-shift Heilbronn coset. Its elements
are exactly the nonzero Teichmuller lifts. This lets generic finite-set
correlation estimates use the existing coset definitions without new data. -/
noncomputable def heilbronnElements (p : ℕ) [Fact p.Prime] : Finset (ZMod (p ^ 2)) := by
  classical exact (shiftedTeichCoset p 0).toFinset

/-- Membership in the finite Heilbronn set agrees with coset membership.
Expand the finite presentation; used for all incidence identifications. -/
theorem mem_heilbronnElements {p : ℕ} [Fact p.Prime] (x : ZMod (p ^ 2)) :
    x ∈ heilbronnElements p ↔ x ∈ shiftedTeichCoset p 0 := by classical exact Set.mem_toFinset

/-- A difference pair is uniquely specified by its second coordinate y,
with d+y still in the Heilbronn set. The explicit equivalence identifies
the old fiber cardinality with a translated incidence column. -/
noncomputable def heilbronnDifferenceIncidenceEquiv {p : ℕ} [Fact p.Prime] (d : ZMod (p ^ 2)) :
    cosetDifferenceAt p 0 0 d ≃ { y : heilbronnElements p // d + y.val ∈ heilbronnElements p } := by
  refine
    { toFun := fun z ↦ ⟨⟨z.val.2, (mem_heilbronnElements _).mpr z.property.2.1⟩, ?_⟩
      invFun := fun y ↦
        ⟨(d + y.val.val, y.val.val), (mem_heilbronnElements _).mp y.property,
          (mem_heilbronnElements _).mp y.val.property, add_sub_cancel_right d y.val.val⟩
      left_inv := ?_
      right_inv := ?_ }
  · apply (mem_heilbronnElements _).mpr
    change d + z.val.2 ∈ shiftedTeichCoset p 0
    rw [← eq_add_of_sub_eq z.property.2.2]
    exact z.property.1
  · intro z
    apply Subtype.ext
    apply Prod.ext
    · exact (eq_add_of_sub_eq z.property.2.2).symm
    · rfl
  · intro y
    rfl

/-- The existing Heilbronn correlation is exactly the generic finite-set
difference correlation. Count the incidence equivalence by an indicator
sum. This transfers the finite matrix amplification to the existing energy. -/
theorem heilbronn_correlation_eq_finiteDifferenceCorrelation {p : ℕ} [Fact p.Prime]
    (d : ZMod (p ^ 2)) :
    Nat.card (cosetDifferenceAt p 0 0 d) =
      PseudoPrime.Analysis.finiteDifferenceCorrelation (heilbronnElements p) d := by
  classical
    rw [Nat.card_congr (heilbronnDifferenceIncidenceEquiv d), Nat.card_eq_fintype_card,
    Fintype.card_subtype, PseudoPrime.Analysis.finiteDifferenceCorrelation_eq_subtype,
    Finset.sum_boole, Nat.cast_id]

/-- The finite Heilbronn set has p-1 elements. Use its coset presentation
and the already proved coset cardinality; this fixes the amplification scale. -/
theorem card_heilbronnElements {p : ℕ} [Fact p.Prime] : (heilbronnElements p).card = p - 1 := by
  classical
    rw [heilbronnElements, Set.toFinset_card, ← Nat.card_eq_fintype_card, card_shiftedTeichCoset]

/-- Negating a difference preserves its ordered-pair count, including zero.
Use the translated incidence formula and commute the two indicator factors.
This proves evenness for every correlation weight used in amplification. -/
theorem heilbronn_correlation_neg {p : ℕ} [Fact p.Prime] (a : ZMod (p ^ 2)) :
    Nat.card (cosetDifferenceAt p 0 0 (-a)) = Nat.card (cosetDifferenceAt p 0 0 a) := by
  rw [heilbronn_correlation_eq_finiteDifferenceCorrelation,
    heilbronn_correlation_eq_finiteDifferenceCorrelation]
  have h₁ := PseudoPrime.Analysis.finite_incidence_overlap (heilbronnElements p) 0 a
  have h₂ := PseudoPrime.Analysis.finite_incidence_overlap (heilbronnElements p) a 0
  rw [zero_sub] at h₁
  rw [sub_zero] at h₂
  rw [← h₁, ← h₂]
  apply Finset.sum_congr rfl
  intro b _
  exact Nat.mul_comm _ _

end PseudoPrime.NumberTheory.Heilbronn
