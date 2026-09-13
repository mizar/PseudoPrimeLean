/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.NumberTheory.Jacobi.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# Quadratic Dirichlet characters attached to odd moduli

This file begins the character-theoretic layer by descending the numerator variable of the
Jacobi symbol to `ZMod n`.  Multiplicativity and vanishing on nonunits are inherited from the
corresponding Jacobi-symbol theorems.
-/

namespace PseudoPrime.NumberTheory

/--
For odd `n`, `PseudoPrime.NumberTheory.jacobiNumeratorCharacter n hn` is the Dirichlet character
modulo `n` whose value on a residue class represented by `a` is `J(a | n)`.
-/
def jacobiNumeratorCharacter (n : ℕ) (hn : Odd n) : DirichletCharacter ℤ n := by
  let _ : NeZero n :=
    ⟨by
      have hnmod : n % 2 = 1 := Nat.odd_iff.mp hn
      omega⟩
  exact
    { toFun := fun a => jacobiSym a.val n
      map_one' := by
        rw [ZMod.val_one_eq_one_mod]
        have hmod : ((1 % n : ℕ) : ℤ) % n = (1 : ℤ) % n := by
          simp only [Int.natCast_emod, Nat.cast_one]
          rw [Int.emod_emod]
        rw [jacobiSym.mod_left' hmod, jacobiSym.one_left]
      map_mul' := by
        intro a b
        rw [ZMod.val_mul]
        have hmod : (((a.val * b.val) % n : ℕ) : ℤ) % n = ((a.val : ℤ) * b.val) % n := by
          simp only [Int.natCast_emod, Nat.cast_mul]
          rw [Int.emod_emod]
        rw [jacobiSym.mod_left' hmod, jacobiSym.mul_left]
      map_nonunit' := by
        intro a ha
        have hnoncop : ¬Nat.Coprime a.val n := by
          intro hcop
          apply ha
          rw [← ZMod.natCast_zmod_val a]
          exact (ZMod.isUnit_iff_coprime a.val n).mpr hcop
        have hgcd : (a.val : ℤ).gcd n ≠ 1 := by
          rw [Int.gcd_eq_natAbs, Int.natAbs_natCast]
          exact hnoncop
        exact jacobi_eq_zero_iff_not_coprime.mpr hgcd }

/-- Evaluation on the canonical representative is the defining Jacobi symbol. -/
theorem jacobiNumeratorCharacter_apply_val (n : ℕ) (hn : Odd n) (a : ZMod n) :
    jacobiNumeratorCharacter n hn a = jacobiSym a.val n :=
  rfl

/-- The character evaluated at a natural number is its Jacobi symbol modulo `n`. -/
theorem jacobiNumeratorCharacter_apply_natCast (n : ℕ) (hn : Odd n) (a : ℕ) :
    jacobiNumeratorCharacter n hn (a : ZMod n) = jacobiSym a n := by
  rw [jacobiNumeratorCharacter_apply_val, ZMod.val_natCast]
  apply jacobiSym.mod_left'
  simp only [Int.natCast_emod]
  rw [Int.emod_emod]

/-- The Jacobi numerator character lifted from level `n` to level `4 * n`. -/
noncomputable def liftedJacobiNumeratorCharacter (n : ℕ) (hn : Odd n) :
    DirichletCharacter ℤ (4 * n) :=
  DirichletCharacter.changeLevel (R := ℤ) (n.dvd_mul_left 4)
    (jacobiNumeratorCharacter n hn)

/-- The character `χ₄` lifted from level `4` to level `4 * n`. -/
noncomputable def liftedChiFour (n : ℕ) : DirichletCharacter ℤ (4 * n) :=
  DirichletCharacter.changeLevel (R := ℤ) (Nat.dvd_mul_right 4 n) ZMod.χ₄

/--
The real quadratic character at level `4 * n`: for `n = 1 mod 4` it is the lifted Jacobi
numerator character, while the other odd residue class includes the lifted `χ₄` factor.
-/
noncomputable def quadraticCharacter (n : ℕ) (hn : Odd n) : DirichletCharacter ℤ (4 * n) :=
  if n % 4 = 1 then liftedJacobiNumeratorCharacter n hn
  else
    liftedJacobiNumeratorCharacter n hn *
      liftedChiFour n

/-- The quadratic character with its integer values embedded into the complex numbers. -/
noncomputable def complexQuadraticCharacter (n : ℕ) (hn : Odd n) : DirichletCharacter ℂ (4 * n) :=
  (quadraticCharacter n hn).ringHomComp (Int.castRingHom ℂ)

/-- Evaluation of the complex character is the complex cast of the integer-valued character. -/
theorem complexQuadraticCharacter_apply (n : ℕ) (hn : Odd n) (a : ZMod (4 * n)) :
    complexQuadraticCharacter n hn a =
      (quadraticCharacter n hn a : ℂ) :=
  rfl

/-- Evaluation of the lifted Jacobi character at an integer coprime to `4 * n`. -/
theorem liftedJacobiNumeratorCharacter_apply_of_coprime (n : ℕ) (hn : Odd n) {a : ℕ}
    (ha : Nat.Coprime a (4 * n)) :
    liftedJacobiNumeratorCharacter n hn ((a : ℤ) : ZMod (4 * n)) =
      jacobiSym a n := by
  rw [liftedJacobiNumeratorCharacter,
    DirichletCharacter.changeLevel_eq_cast_of_dvd'
      (jacobiNumeratorCharacter n hn) (n.dvd_mul_left 4) ha.isCoprime]
  simpa only [Int.cast_natCast] using
    jacobiNumeratorCharacter_apply_natCast n hn a

/-- Evaluation of the lifted `χ₄` factor at an integer coprime to `4 * n`. -/
theorem liftedChiFour_apply_of_coprime (n : ℕ) {a : ℕ} (ha : Nat.Coprime a (4 * n)) :
    liftedChiFour n ((a : ℤ) : ZMod (4 * n)) =
      ZMod.χ₄ ((a : ℤ) : ZMod 4) := by
  rw [liftedChiFour,
    DirichletCharacter.changeLevel_eq_cast_of_dvd' ZMod.χ₄ (Nat.dvd_mul_right 4 n) ha.isCoprime]

/-- Coprime evaluation formula for `PseudoPrime.NumberTheory.quadraticCharacter`
before quadratic reciprocity is applied. -/
theorem quadraticCharacter_apply_of_coprime (n : ℕ) (hn : Odd n) {a : ℕ}
    (ha : Nat.Coprime a (4 * n)) :
    quadraticCharacter n hn ((a : ℤ) : ZMod (4 * n)) =
      if n % 4 = 1 then jacobiSym a n else jacobiSym a n * ZMod.χ₄ ((a : ℤ) : ZMod 4) := by
  by_cases hn4 : n % 4 = 1
  · simp only [quadraticCharacter, hn4, ite_true,
      liftedJacobiNumeratorCharacter_apply_of_coprime n hn ha]
  · simp only [quadraticCharacter, hn4, ite_false, MulChar.mul_apply,
      liftedJacobiNumeratorCharacter_apply_of_coprime n hn ha,
      liftedChiFour_apply_of_coprime n ha]

end PseudoPrime.NumberTheory
