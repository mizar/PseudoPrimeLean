/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.DirichletCharacter.Basic

/-! # Seven-eighths nonvanishing for a Hecke family -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.GRH

/-- The ring of integers of the third cyclotomic field over the rationals. -/
abbrev HeckeIntegerRing :=
  NumberField.RingOfIntegers (CyclotomicField 3 ℚ)

instance : IsCyclotomicExtension {3} ℚ (CyclotomicField 3 ℚ) :=
  CyclotomicField.isCyclotomicExtension 3 ℚ

/-- A character of the concrete Hecke family used in the seven-eighths challenge.
The modulus is a nonzero ideal, the residue character is trivial on units, and
the positive period lies in the modulus. -/
structure HeckeCharacter where
  modulus : Ideal HeckeIntegerRing
  modulus_ne_bot : modulus ≠ ⊥
  residue : MulChar (HeckeIntegerRing ⧸ modulus) ℂ
  unit_trivial :
    ∀ u : HeckeIntegerRingˣ, residue (Ideal.Quotient.mk modulus (u : HeckeIntegerRing)) = 1
  period : ℕ
  period_pos : 0 < period
  period_mem : (period : HeckeIntegerRing) ∈ modulus

instance (χ : HeckeCharacter) : NeZero χ.period :=
  ⟨Nat.ne_of_gt χ.period_pos⟩

/-- The chosen primitive cube root of unity as an algebraic integer. It fixes
the coordinates used by the lattice continuation of the Hecke L-function. -/
noncomputable def heckeOmega : HeckeIntegerRing :=
  (IsCyclotomicExtension.zeta_spec 3 ℚ (CyclotomicField 3 ℚ)).toInteger

/-- The lattice point with integral coordinates `x` and `y`, expressed in
the basis consisting of one and the chosen primitive cube root. -/
noncomputable def heckeCoordinate (x y : ℤ) : HeckeIntegerRing :=
  (x : HeckeIntegerRing) + (y : HeckeIntegerRing) * heckeOmega

/-- Evaluate the residue character of `χ` at an algebraic integer. -/
noncomputable def HeckeCharacter.elementCoeff (χ : HeckeCharacter) (z : HeckeIntegerRing) : ℂ :=
  χ.residue (Ideal.Quotient.mk χ.modulus z)

/-- The periodic coefficient on the square of residue coordinates used by
the lattice construction of the L-function. -/
noncomputable def HeckeCharacter.coefficients (χ : HeckeCharacter)
    (a : Fin χ.period × Fin χ.period) : ℂ :=
  χ.elementCoeff (heckeCoordinate a.1 a.2)

/-- For a specified continuation of the L-function of this Hecke family,
assert nonvanishing on `7/8 < s.re` away from the principal-character pole.
The continuation is an explicit parameter until the lattice construction of
the comparator challenge has been formalized. -/
def HeckeQuasiRiemannHypothesis (L : HeckeCharacter → ℂ → ℂ) : Prop :=
  ∀ (χ : HeckeCharacter) (s : ℂ), (7 / 8 : ℝ) < s.re → ¬(χ.residue = 1 ∧ s = 1) → L χ s ≠ 0

end PseudoPrime.AnalyticNumberTheory.GRH
