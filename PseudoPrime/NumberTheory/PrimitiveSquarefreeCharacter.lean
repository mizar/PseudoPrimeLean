/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.JacobiCharacterArithmetic

/-! # Primitive quadratic character values after removing square factors -/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- For an odd nonsquare input and its standard squarefree decomposition,
the complex quadratic character is induced from that of the squarefree part.
Compare the integer-valued characters on units and compose with the complex cast.
This allows primitive values to be compared at every integer, not only at units. -/
theorem complexQuadraticCharacter_eq_squarefree_changeLevel {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : JacobiCharacterArithmeticData n hn hns) (hdvd : 4 * bridge.squarefreePart ∣ 4 * n) :
    complexQuadraticCharacter n hn =
      DirichletCharacter.changeLevel hdvd
        (complexQuadraticCharacter bridge.squarefreePart bridge.squarefreePart_odd) := by
  let : NeZero (4 * n) := ⟨mul_ne_zero (by norm_num only) hn.pos.ne'⟩
  apply MulChar.ext
  intro u
  let a := (u : ZMod (4 * n)).val
  have hc : Nat.Coprime a (4 * n) := ZMod.val_coe_unit_coprime u
  have hu : ((a : ℤ) : ZMod (4 * n)) = (u : ZMod (4 * n)) := by
    simp only [a, ZMod.natCast_val, ZMod.intCast_zmod_cast]
  rw [← hu, DirichletCharacter.changeLevel_eq_cast_of_dvd' _ hdvd hc.isCoprime,
    complexQuadraticCharacter_apply, complexQuadraticCharacter_apply]
  have he := quadraticCharacter_eq_squarefreePart_changeLevel_apply_of_coprime bridge hdvd hc
  rw [DirichletCharacter.changeLevel_eq_cast_of_dvd' _ hdvd hc.isCoprime] at he
  exact congrArg (fun z : ℤ ↦ (z : ℂ)) he

/-- Primitive quadratic values of an odd nonsquare equal those of its squarefree
part at every integer. Express the lifted character as a change of level, then
use invariance of primitive values. No coprimality with the original input is needed. -/
theorem primitiveQuadraticCharacter_eq_squarefree_apply {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : JacobiCharacterArithmeticData n hn hns) (a : ℤ) :
    primitiveQuadraticCharacter n hn a =
      primitiveQuadraticCharacter bridge.squarefreePart bridge.squarefreePart_odd a := by
  let : NeZero (4 * n) := ⟨mul_ne_zero (by norm_num only) hn.pos.ne'⟩
  have hd : bridge.squarefreePart ∣ n :=
    ⟨bridge.squareFactor ^ 2, by simpa only [mul_comm] using bridge.squarefreePart_sq_mul.symm⟩
  have hdvd := Nat.mul_dvd_mul_left 4 hd
  change (complexQuadraticCharacter n hn).primitiveCharacter a = _
  rw [complexQuadraticCharacter_eq_squarefree_changeLevel bridge hdvd]
  exact DirichletCharacter.primitiveCharacter_changeLevel_apply hdvd _ a

/-- At an odd prime not dividing the squarefree part, the primitive character
has the Jacobi value of that part, even if the prime divides the original input.
Transfer the primitive value to the squarefree input and use its prime evaluation. -/
theorem primitiveQuadraticCharacter_apply_squarefree_odd_prime {n p : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} (bridge : JacobiCharacterArithmeticData n hn hns) (hp : p.Prime)
    (ho : Odd p) (hd : ¬p ∣ bridge.squarefreePart) :
    primitiveQuadraticCharacter n hn (p : ℤ) = (jacobiSym bridge.squarefreePart p : ℂ) := by
  rw [primitiveQuadraticCharacter_eq_squarefree_apply bridge]
  exact primitiveQuadraticCharacter_apply_odd_prime bridge.squarefreePart_odd hp ho hd

end PseudoPrime.NumberTheory
