/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.MulChar.Basic
public import Mathlib.Algebra.Group.Subgroup.Ker

/-! # Proper unit kernels of nonprincipal multiplicative characters

Nonprincipality is detected on units, so the kernel of the induced unit
homomorphism is proper. No quadraticity or finiteness assumption is needed.
-/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- For a nonprincipal multiplicative character between the displayed commutative
monoids, the kernel of its unit homomorphism is proper. If the kernel were top,
all unit values would be one, and character extensionality would give principality.
This supplies the algebraic premise for general-character subgroup witness bounds. -/
theorem ker_toUnitHom_ne_top_of_ne_one {R R' : Type*} [CommMonoid R] [CommMonoidWithZero R']
    (χ : MulChar R R') (hne : χ ≠ 1) : χ.toUnitHom.ker ≠ ⊤ := by
  intro he
  apply hne
  apply MulChar.ext
  intro u
  have hk : u ∈ χ.toUnitHom.ker := he.symm ▸ Subgroup.mem_top u
  have hh := congrArg Units.val (MonoidHom.mem_ker.mp hk)
  simpa only [MulChar.coe_toUnitHom, Units.val_one, MulChar.one_apply_coe] using hh

end PseudoPrime.NumberTheory
