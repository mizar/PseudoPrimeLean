/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.DirichletCharacter

/-! # Small levels and conductors of Dirichlet characters

The unit group at level two is trivial. Consequently a nonprincipal character
at a nonzero level has conductor at least three.
-/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- Every Dirichlet character at level two is principal, since its unit group
has a single element. Extensionality on units reduces all values to the value
at one. This excludes level two for primitive characters. -/
theorem dirichletCharacter_level_two_eq_one {R : Type*} [CommMonoidWithZero R]
    (χ : DirichletCharacter R 2) : χ = 1 := by
  apply MulChar.ext
  intro u
  have hu : u = 1 := Subsingleton.elim _ _
  rw [hu, Units.val_one, χ.map_one, map_one]

/-- A primitive Dirichlet character cannot have level two. Its conductor would
equal two by primitivity, but the only level-two character has conductor one.
This removes the small conductor exception from analytic estimates. -/
theorem dirichletCharacter_level_ne_two_of_isPrimitive {R : Type*} [CommMonoidWithZero R] {m : ℕ}
    (χ : DirichletCharacter R m) (hp : χ.IsPrimitive) : m ≠ 2 := by
  intro hm
  subst m
  have hc := (DirichletCharacter.isPrimitive_def χ).mp hp
  rw [dirichletCharacter_level_two_eq_one χ, DirichletCharacter.conductor_one] at hc
  norm_num only at hc

/-- A nonprincipal character at a nonzero level has conductor at least three.
Its conductor is positive, differs from one by the principal-character
criterion, and differs from two by primitive normalization.
This supplies the conductor hypothesis in explicit character-sum bounds. -/
theorem three_le_conductor_of_ne_one {R : Type*} [CommMonoidWithZero R] {q : ℕ} [NeZero q]
    (χ : DirichletCharacter R q) (hne : χ ≠ 1) : 3 ≤ χ.conductor := by
  have h1 : χ.conductor ≠ 1 := fun h => hne (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr h)
  have h2 :=
    dirichletCharacter_level_ne_two_of_isPrimitive χ.primitiveCharacter
      (DirichletCharacter.primitiveCharacter_isPrimitive χ)
  have hc1 : 1 ≤ χ.conductor := Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero χ.conductor_ne_zero)
  have hc2 := Nat.succ_le_iff.mpr (lt_of_le_of_ne hc1 (Ne.symm h1))
  exact Nat.succ_le_iff.mpr (lt_of_le_of_ne hc2 (Ne.symm h2))

end PseudoPrime.NumberTheory
