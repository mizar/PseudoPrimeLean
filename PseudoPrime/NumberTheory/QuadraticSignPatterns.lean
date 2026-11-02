/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.QuadraticCharacterKernel

/-! # Simultaneous signs of independent quadratic characters

Distinct nonprincipal quadratic complex multiplicative characters realize both mixed
unit-sign patterns. Their product unit also realizes the two negative signs. The result
is valid over any commutative monoid with zero, independently of a modulus or analytic
kernel. It supports quadratic-character independence and finite Fourier sign tests.
-/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- A quadratic complex multiplicative character has sign one or minus one at a unit.
Input: quadraticity and a unit over any commutative monoid with zero. Coerce the existing
unit-hom sign dichotomy back to complex values. This supplies simultaneous sign constructions. -/
private theorem quadratic_unit_sign {R : Type*} [CommMonoidWithZero R] (χ : MulChar R ℂ)
    (hq : χ.IsQuadratic) (u : Rˣ) : χ (u : R) = 1 ∨ χ (u : R) = -1 :=
  Or.elim (quadratic_toUnitHom_eq_one_or_neg_one χ hq u)
    (fun h ↦ Or.inl ((MulChar.coe_toUnitHom χ u).symm.trans (congrArg Units.val h)))
    (fun h ↦ Or.inr ((MulChar.coe_toUnitHom χ u).symm.trans (congrArg Units.val h)))

/-- One mixed sign and a nonprincipal second character yield the opposite mixed sign.
Input: quadratic characters, a unit with signs minus/plus and nonprincipality of the second.
Choose a unit where its sign is negative; if necessary multiply by the known unit to flip
the first sign. This completes independent quadratic sign patterns. -/
private theorem complete_unit_signs {R : Type*} [CommMonoidWithZero R] (a b : MulChar R ℂ)
    (ha : a.IsQuadratic) (hb : b.IsQuadratic) (hb1 : b ≠ 1) (u : Rˣ) (hau : a (u : R) = -1)
    (hbu : b (u : R) = 1) : ∃ v : Rˣ, a (v : R) = 1 ∧ b (v : R) = -1 := by
  obtain ⟨v, hv⟩ := MulChar.ne_one_iff.mp hb1
  have hbv := (quadratic_unit_sign b hb v).resolve_left hv
  rcases quadratic_unit_sign a ha v with hav | hav
  · exact ⟨v, hav, hbv⟩
  · refine ⟨u * v, ?_, ?_⟩
    · rw [Units.val_mul, map_mul, hau, hav, neg_mul_neg, one_mul]
    · rw [Units.val_mul, map_mul, hbu, hbv, one_mul]

/-- Distinct multiplicative characters differ at an actual unit.
Input: character inequality over a commutative monoid with zero. Unit-value equality would
imply character equality by multiplicative-character extensionality. This supplies separation. -/
private theorem exists_unit_values_ne {R : Type*} [CommMonoidWithZero R] (a b : MulChar R ℂ)
    (hab : a ≠ b) : ∃ u : Rˣ, a (u : R) ≠ b (u : R) :=
  Classical.byContradiction fun h ↦
    hab (MulChar.ext fun u ↦ Classical.byContradiction fun hu ↦ h ⟨u, hu⟩)

/-- Distinct nonprincipal quadratic characters realize both mixed unit-sign patterns.
Input: quadraticity, nonprincipality and distinctness over any commutative monoid with zero.
Separate the characters at one unit, classify its two signs and complete the opposite pattern.
This gives actual independent sign values for quadratic reciprocity and finite Fourier tests. -/
theorem quadratic_unit_sign_patterns {R : Type*} [CommMonoidWithZero R] (a b : MulChar R ℂ)
    (ha : a.IsQuadratic) (hb : b.IsQuadratic) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) :
    ∃ u v : Rˣ, a (u : R) = -1 ∧ b (u : R) = 1 ∧ a (v : R) = 1 ∧ b (v : R) = -1 := by
  obtain ⟨u, hu⟩ := exists_unit_values_ne a b hab
  rcases quadratic_unit_sign a ha u with hau | hau <;>
    rcases quadratic_unit_sign b hb u with hbu | hbu
  · exact False.elim (hu (hau.trans hbu.symm))
  · obtain ⟨v, hvb, hva⟩ := complete_unit_signs b a hb ha ha1 u hbu hau
    exact ⟨v, u, hva, hvb, hau, hbu⟩
  · obtain ⟨v, hva, hvb⟩ := complete_unit_signs a b ha hb hb1 u hau hbu
    exact ⟨u, v, hau, hbu, hva, hvb⟩
  · exact False.elim (hu (hau.trans hbu.symm))

end PseudoPrime.NumberTheory
