/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.MulChar.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Set.Card

/-! # Unit kernels of nonprincipal complex quadratic characters -/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- A complex quadratic character takes the values one or minus one on a unit.
The zero branch is impossible because the induced value is a unit.
This identifies the possible image values of its unit homomorphism. -/
theorem quadratic_toUnitHom_eq_one_or_neg_one {R : Type*} [CommMonoidWithZero R] (χ : MulChar R ℂ)
    (hq : χ.IsQuadratic) (u : Rˣ) : χ.toUnitHom u = 1 ∨ χ.toUnitHom u = -1 := by
  rcases hq u with hz | h1 | hn
  · have h0 : χ u ≠ 0 := by simpa only [MulChar.coe_toUnitHom] using (Units.ne_zero (χ.toUnitHom u))
    exact (h0 hz).elim
  · exact Or.inl (Units.ext h1)
  · exact Or.inr (Units.ext hn)

/-- For a nonprincipal complex quadratic character, the unit image is exactly {1,−1}.
Nonprincipality supplies a unit with non-one value, necessarily minus one.
This computes the image used to count the character kernel index. -/
theorem range_toUnitHom_of_quadratic_ne_one {R : Type*} [CommMonoidWithZero R] (χ : MulChar R ℂ)
    (hq : χ.IsQuadratic) (hne : χ ≠ 1) : (χ.toUnitHom.range : Set ℂˣ) = {1, -1} := by
  obtain ⟨u, hu⟩ := MulChar.ne_one_iff.mp hne
  have hneg : χ.toUnitHom u = -1 :=
    (quadratic_toUnitHom_eq_one_or_neg_one χ hq u).resolve_left
      (fun he ↦ hu (congrArg Units.val he))
  ext z
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨v, rfl⟩
    exact quadratic_toUnitHom_eq_one_or_neg_one χ hq v
  · rintro (rfl | rfl)
    · exact ⟨1, map_one _⟩
    · exact ⟨u, hneg⟩

/-- The unit kernel of a nonprincipal complex quadratic character has index two.
Use the kernel-image index formula and the two distinct image values.
This supplies the exact subgroup index in quadratic prime-witness comparisons. -/
theorem index_ker_toUnitHom_of_quadratic_ne_one {R : Type*} [CommMonoidWithZero R] (χ : MulChar R ℂ)
    (hq : χ.IsQuadratic) (hne : χ ≠ 1) : χ.toUnitHom.ker.index = 2 := by
  rw [Subgroup.index_ker]
  change Nat.card (χ.toUnitHom.range : Set ℂˣ) = 2
  rw [range_toUnitHom_of_quadratic_ne_one χ hq hne, Nat.card_coe_set_eq]
  apply Set.ncard_pair
  intro he
  have h := congrArg Units.val he
  norm_num only [Units.val_one, Units.val_neg] at h

end PseudoPrime.NumberTheory
