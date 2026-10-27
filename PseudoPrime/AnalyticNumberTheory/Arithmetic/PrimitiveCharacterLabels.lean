/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.DirichletCharacter.Bounds
public import Mathlib.Analysis.Complex.Basic

/-! # Injective conductor and primitive-character labels -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- Attach the conductor and primitive character to a character at a fixed level.
The dependent pair retains both labels and recovers the original character by
change of level. It is used to reindex finite error sums without multiplicity loss. -/
noncomputable def primitiveCharacterLabel {q : ℕ} (χ : DirichletCharacter ℂ q) :
    Σ d : ℕ, DirichletCharacter ℂ d :=
  ⟨χ.conductor, χ.primitiveCharacter⟩

/-- At a fixed level, conductor and primitive-character labels determine the
original character. Recover it by change of level using the conductor divisibility
proof, giving a left inverse. Thus finite family reindexing introduces no extra factor. -/
theorem primitiveCharacterLabel_injective (q : ℕ) :
    Function.Injective (primitiveCharacterLabel (q := q)) := by
  classical
  have hleft :
    Function.LeftInverse
      (fun p : (Σ d : ℕ, DirichletCharacter ℂ d) ↦
        if h : p.1 ∣ q then DirichletCharacter.changeLevel h p.2 else 1)
      (primitiveCharacterLabel (q := q)) := by
    intro χ
    dsimp only [primitiveCharacterLabel]
    rw [dite_eq_left χ.conductor_dvd_level]
    exact χ.changeLevel_primitiveCharacter
  exact hleft.injective

/-- A nonprincipal character has nonprincipal primitive character. Otherwise its
change of level would be principal as well. This supplies the nonprincipal
hypothesis when transferring arithmetic errors to their primitive source. -/
theorem primitiveCharacter_ne_one_of_ne_one {q : ℕ} {χ : DirichletCharacter ℂ q} (hne : χ ≠ 1) :
    χ.primitiveCharacter ≠ 1 := by
  intro h
  apply hne
  rw [← χ.changeLevel_primitiveCharacter, h, map_one]

open Classical in
/-- Every primitive label from a finite nonprincipal family has positive conductor
dividing and bounded by the nonzero original level, and a primitive nonprincipal
character. Extract the original character from image membership. These properties
place the reindexed family in the conductor-bounded analytic ledger. -/
theorem primitiveCharacterLabel_image_properties {q : ℕ} [NeZero q]
    (S : Finset (DirichletCharacter ℂ q)) (hne : ∀ χ ∈ S, χ ≠ 1)
    {p : Σ d : ℕ, DirichletCharacter ℂ d} (hp : p ∈ S.image primitiveCharacterLabel) :
    p.1 ∣ q ∧ 0 < p.1 ∧ p.1 ≤ q ∧ p.2.IsPrimitive ∧ p.2 ≠ 1 := by
  obtain ⟨χ, hχ, rfl⟩ := Finset.mem_image.mp hp
  exact
    ⟨χ.conductor_dvd_level, Nat.pos_of_ne_zero χ.conductor_ne_zero,
      Nat.le_of_dvd (NeZero.pos q) χ.conductor_dvd_level, χ.primitiveCharacter_isPrimitive,
      primitiveCharacter_ne_one_of_ne_one (hne χ hχ)⟩

end PseudoPrime.AnalyticNumberTheory.Arithmetic
