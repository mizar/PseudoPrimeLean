/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.NumberTheory.JacobiCharacterPrimeEvaluation
import PseudoPrime.NumberTheory.MulCharParity

/-!
# Primitive quadratic characters

This file replaces the complex quadratic character at level `4 * n` by its associated primitive
character at the conductor.  Values at integers coprime to the original level are unchanged,
and nontriviality for odd nonsquare moduli descends to the primitive character.
-/

namespace PseudoPrime.NumberTheory

/-- The primitive character inducing `PseudoPrime.NumberTheory.complexQuadraticCharacter n hn`. -/
noncomputable def primitiveQuadraticCharacter (n : ℕ) (hn : Odd n) :
    DirichletCharacter ℂ (complexQuadraticCharacter n hn).conductor :=
  (complexQuadraticCharacter n hn).primitiveCharacter

/--
The complex quadratic character attached to an odd modulus is even.  The proof evaluates it at
`-1` using the representative `4 * n - 1`; the two residue classes modulo `4` are exactly
compensated by the `χ₄` factor in `PseudoPrime.NumberTheory.quadraticCharacter`.
-/
theorem complexQuadraticCharacter_isEven (n : ℕ) (hn : Odd n) :
    (complexQuadraticCharacter n hn).Even := by
  unfold DirichletCharacter.Even
  have hnpos : 0 < n := Odd.pos hn
  let a := 4 * n - 1
  have ha : 1 ≤ 4 * n := by omega
  have hcop : Nat.Coprime a (4 * n) := by
    rw [Nat.coprime_comm, Nat.coprime_self_sub_right ha]
    exact Nat.coprime_one_right _
  have hcast : (a : ZMod (4 * n)) = -1 := by
    dsimp only [a]
    rw [Nat.cast_sub ha]
    simp only [CharP.cast_eq_zero, Nat.cast_one, zero_sub]
  rw [← hcast, complexQuadraticCharacter_apply]
  have hval := quadraticCharacter_apply_of_coprime n hn hcop
  have hval' :
    quadraticCharacter n hn (a : ZMod (4 * n)) =
      if n % 4 = 1 then jacobiSym a n else jacobiSym a n * ZMod.χ₄ (a : ZMod 4) := by
    simpa only [Int.cast_natCast] using hval
  rw [hval']
  have hmod : (a : ℤ) % (n : ℤ) = (-1 : ℤ) % n := by
    dsimp only [a]
    rw [Nat.cast_sub ha]
    simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, Int.mul_sub_emod_self_right,
      Int.reduceNeg]
  have hj : jacobiSym a n = jacobiSym (-1) n := jacobiSym.mod_left' hmod
  rw [hj, jacobiSym.at_neg_one hn]
  have ha_mod : a % 4 = 3 := by
    dsimp only [a]
    omega
  have ha_even : a % 2 = 1 := by
    dsimp only [a]
    omega
  have hn_odd : n % 2 = 1 := Nat.odd_iff.mp hn
  by_cases h : n % 4 = 1
  · simp only [h, ↓reduceIte, ZMod.χ₄_nat_one_mod_four h, Int.cast_one]
  · have hnmod : n % 4 = 3 := by omega
    rw [ZMod.χ₄_nat_eq_if_mod_four, ZMod.χ₄_nat_eq_if_mod_four]
    simp only [hnmod, OfNat.ofNat_ne_one, ↓reduceIte, hn_odd, one_ne_zero, Int.reduceNeg, ha_even,
      ha_mod, mul_neg, mul_one, neg_neg, Int.cast_one]

/-- The associated character is primitive at its conductor. -/
theorem primitiveQuadraticCharacter_isPrimitive (n : ℕ) (hn : Odd n) :
    (primitiveQuadraticCharacter n hn).IsPrimitive :=
  DirichletCharacter.primitiveCharacter_isPrimitive (complexQuadraticCharacter n hn)

/-- The conductor of the complex quadratic character is nonzero for odd `n`. -/
theorem complexQuadraticCharacter_conductor_ne_zero (n : ℕ) (hn : Odd n) :
    (complexQuadraticCharacter n hn).conductor ≠ 0 := by
  let _ : NeZero (4 * n) := ⟨Nat.mul_ne_zero (by norm_num only) (Odd.pos hn).ne'⟩
  exact DirichletCharacter.conductor_ne_zero (complexQuadraticCharacter n hn)

/-- The conductor of the complex quadratic character carries its canonical nonzero instance. -/
instance complexQuadraticCharacterConductorNeZero (n : ℕ) (hn : Odd n) :
    NeZero (complexQuadraticCharacter n hn).conductor :=
  ⟨complexQuadraticCharacter_conductor_ne_zero n hn⟩

/--
At every integer coprime to the original level `4 * n`, the primitive character has the same
value as the complex quadratic character that it induces.
-/
theorem primitiveQuadraticCharacter_apply_of_isCoprime (n : ℕ) (hn : Odd n) {a : ℤ}
    (ha : IsCoprime a (4 * n)) :
    primitiveQuadraticCharacter n hn a = complexQuadraticCharacter n hn a :=
  DirichletCharacter.primitiveCharacter_apply_of_isCoprime (complexQuadraticCharacter n hn) ha

/-- The primitive character preserves the even parity of its inducing character. -/
theorem primitiveQuadraticCharacter_isEven (n : ℕ) (hn : Odd n) :
    (primitiveQuadraticCharacter n hn).Even := by
  unfold DirichletCharacter.Even
  have hcop : IsCoprime (-1 : ℤ) (4 * (n : ℤ)) := by
    rw [IsCoprime.neg_left_iff]
    exact isCoprime_one_left
  have hval := primitiveQuadraticCharacter_apply_of_isCoprime n hn hcop
  have hvalue : complexQuadraticCharacter n hn (-1 : ZMod (4 * n)) = 1 := by
    simpa only [DirichletCharacter.Even] using complexQuadraticCharacter_isEven n hn
  have hval' :
    primitiveQuadraticCharacter n hn (-1 : ZMod (complexQuadraticCharacter n hn).conductor) =
      complexQuadraticCharacter n hn (-1 : ZMod (4 * n)) := by
    simpa only [Int.cast_neg, Int.cast_one] using hval
  exact hval'.trans hvalue

/--
The primitive character inducing a quadratic character is itself quadratic.

The `changeLevel` map sends `PseudoPrime.NumberTheory.primitiveQuadraticCharacter n hn` back to
`PseudoPrime.NumberTheory.complexQuadraticCharacter n hn`, which squares to `1`; injectivity of
`changeLevel` at the nonzero level `4 * n` then transfers `^2 = 1` down to the primitive character.
-/
theorem primitiveQuadraticCharacter_isQuadratic (n : ℕ) (hn : Odd n) :
    (primitiveQuadraticCharacter n hn).IsQuadratic := by
  let _ : NeZero (4 * n) := ⟨Nat.mul_ne_zero (by norm_num only) (Odd.pos hn).ne'⟩
  rw [MulChar.isQuadratic_iff_sq_eq_one]
  apply
    DirichletCharacter.changeLevel_injective (complexQuadraticCharacter n hn).conductor_dvd_level
  unfold primitiveQuadraticCharacter
  rw [map_pow, DirichletCharacter.changeLevel_primitiveCharacter, map_one]
  exact complexQuadraticCharacter_sq n hn

/--
For an odd nonsquare modulus, the primitive quadratic character is nontrivial.  Otherwise its
change of level would make the original complex quadratic character trivial as well.
-/
theorem primitiveQuadraticCharacter_ne_one_of_not_square (n : ℕ) (hn : Odd n) (hns : ¬IsSquare n) :
    primitiveQuadraticCharacter n hn ≠ 1 := by
  intro hprimitive
  change (complexQuadraticCharacter n hn).primitiveCharacter = 1 at hprimitive
  have hchange := DirichletCharacter.changeLevel_primitiveCharacter (complexQuadraticCharacter n hn)
  rw [hprimitive] at hchange
  simp only [DirichletCharacter.changeLevel_one] at hchange
  exact complexQuadraticCharacter_ne_one_of_not_square n hn hns hchange.symm

end PseudoPrime.NumberTheory
