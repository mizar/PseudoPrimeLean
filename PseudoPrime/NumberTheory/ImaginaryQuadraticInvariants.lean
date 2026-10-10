/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
public import Mathlib.NumberTheory.NumberField.Units.Regulator
public import Mathlib.Tactic

/-!
# Signature and regulator of imaginary quadratic number fields

Negative discriminant and rational degree two force signature `(0, 1)` and regulator one.
These identities specialize the general Dedekind zeta residue formula to the imaginary
quadratic class-number formula.
-/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- A degree-two number field with negative discriminant has no real places and
one complex place. The discriminant sign rules out zero complex places; the
signature degree formula then determines both counts. Used to specialize the
Dedekind zeta residue in the imaginary quadratic class-number formula. -/
theorem imaginaryQuadratic_signature (K : Type) [Field K] [NumberField K]
    (hdeg : Module.finrank ℚ K = 2) (hd : NumberField.discr K < 0) :
    NumberField.InfinitePlace.nrRealPlaces K = 0 ∧
      NumberField.InfinitePlace.nrComplexPlaces K = 1 := by
  have hr := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K
  rw [hdeg] at hr
  have hs := NumberField.sign_discr K
  rw [Int.sign_eq_neg_one_of_neg hd] at hs
  have hc0 : NumberField.InfinitePlace.nrComplexPlaces K ≠ 0 := by
    intro h
    rw [h, pow_zero] at hs
    norm_num only at hs
  have hcpos := Nat.pos_of_ne_zero hc0
  have hc : NumberField.InfinitePlace.nrComplexPlaces K = 1 := by
    nlinarith only [hr, hcpos, Nat.zero_le (NumberField.InfinitePlace.nrRealPlaces K)]
  exact
    ⟨by
      rw [hc] at hr; nlinarith only [hr], hc⟩

/-- The regulator of a degree-two number field with negative discriminant is one.
Its signature gives unit rank zero; the determinant defining the regulator has
an empty index type and equals one. This removes the regulator from the general
Dedekind zeta residue formula without an additional hypothesis. -/
theorem imaginaryQuadratic_regulator_eq_one (K : Type) [Field K] [NumberField K]
    (hdeg : Module.finrank ℚ K = 2) (hd : NumberField.discr K < 0) :
    NumberField.Units.regulator K = 1 := by
  classical
  have hs := imaginaryQuadratic_signature K hdeg hd
  have hr : NumberField.Units.rank K = 0 := by
    rw [NumberField.Units.rank, NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      hs.1, hs.2]
  have hc :
    Fintype.card
        { w : NumberField.InfinitePlace K // w ≠ NumberField.Units.dirichletUnitTheorem.w₀ } =
      0 := by
    rw [← Fintype.card_congr (NumberField.Units.equivFinRank K), Fintype.card_fin, hr]
  rw [NumberField.Units.regulator_eq_det', Matrix.det_eq_one_of_card_eq_zero hc, abs_one]

end PseudoPrime.NumberTheory
