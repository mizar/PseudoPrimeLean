/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimitiveCharacterLabels
public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality

/-! # Fixed-conductor character families have uniformly bounded cardinality -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- A finite set of dependent conductor-character labels all at one fixed level
has cardinality at most the number of characters at that level. Transport each
character to the fixed level; the labels make this map injective. The bound is
independent of any ambient modulus from which the labels were induced. -/
theorem card_fixed_level_character_labels_le (d : ℕ) (S : Finset (Σ m : ℕ, DirichletCharacter ℂ m))
    (hS : ∀ p ∈ S, p.1 = d) : S.card ≤ Fintype.card (DirichletCharacter ℂ d) := by
  classical
  let F : { p // p ∈ S } → DirichletCharacter ℂ d := fun p ↦
    cast (congrArg (DirichletCharacter ℂ) (hS p.val p.property)) p.val.2
  have hf : Function.Injective F := by
    intro p r he
    apply Subtype.ext
    apply Sigma.ext ((hS p.val p.property).trans (hS r.val r.property).symm)
    have hp : F p ≍ p.val.2 := cast_heq _ _
    have hr : F r ≍ r.val.2 := cast_heq _ _
    exact hp.symm.trans ((heq_of_eq he).trans hr)
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective F hf

/-- At a fixed ambient level, a finite family with one specified conductor has
cardinality at most the number of characters modulo that conductor. Use injective
primitive labels and the fixed-level cardinality bound. This prevents a growing
ambient-character factor in the separate conductor-four error. -/
theorem card_character_family_of_fixed_conductor_le {q : ℕ} (S : Finset (DirichletCharacter ℂ q))
    (d : ℕ) (hS : ∀ χ ∈ S, χ.conductor = d) : S.card ≤ Fintype.card (DirichletCharacter ℂ d) := by
  classical
  have hc :=
    card_fixed_level_character_labels_le d (S.image primitiveCharacterLabel)
      (by
        intro p hp
        obtain ⟨χ, hχ, rfl⟩ := Finset.mem_image.mp hp
        exact hS χ hχ)
  rw [Finset.card_image_of_injective S (primitiveCharacterLabel_injective q)] at hc
  exact hc

end PseudoPrime.AnalyticNumberTheory.Arithmetic
