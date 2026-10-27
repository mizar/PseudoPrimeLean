/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.JacobiCharacterArithmetic

/-! # Jacobi character data with a prescribed squarefree decomposition -/

public section

namespace PseudoPrime.NumberTheory

/-- Given an odd nonsquare n=b²d with squarefree d>1, construct the complete
arithmetic character bridge with exactly these factors. The fundamental
discriminant and primitive character are constructed as in the general
existence theorem. This permits bounds uniform over a fixed d input family. -/
theorem exists_jacobiCharacterArithmeticData_of_sq_mul {n d b : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hdgt : 1 < d) (hdsquarefree : Squarefree d) (hfactor : b ^ 2 * d = n) :
    ∃ bridge : JacobiCharacterArithmeticData n hn hns,
      bridge.squarefreePart = d ∧ bridge.squareFactor = b := by
  have hdpos : 0 < d := Nat.lt_trans Nat.zero_lt_one hdgt
  have hbdiv : b ∣ n :=
    ⟨b * d, by
      rw [← hfactor]; ring⟩
  have hbpos : 0 < b := (Odd.of_dvd_nat hn hbdiv).pos
  have hdodd : Odd d := Odd.of_dvd_nat hn ⟨b ^ 2, by simpa only [mul_comm] using hfactor.symm⟩
  let D := positiveFundamentalDiscriminant d
  have hDpos : 0 < D := by
    by_cases hdmod : d % 4 = 1
    · rw [show D = d by
          dsimp only [D]
          exact positiveFundamentalDiscriminant_eq_self hdmod]
      exact hdpos
    · rw [show D = 4 * d by
          dsimp only [D]
          exact positiveFundamentalDiscriminant_eq_four_mul hdmod]
      exact Nat.mul_pos (by norm_num only : 0 < 4) hdpos
  have hdl : d ≤ n := by
    rw [← hfactor]
    have hb1 : 1 ≤ b := Nat.succ_le_of_lt hbpos
    have hbpow : 1 ≤ b ^ 2 := one_le_pow₀ hb1
    simpa only [Nat.mul_comm, ge_iff_le] using Nat.le_mul_of_pos_right d hbpow
  have hDle : D ≤ 4 * n := by
    by_cases hdmod : d % 4 = 1
    · rw [show D = d by
          dsimp only [D]
          exact positiveFundamentalDiscriminant_eq_self hdmod]
      exact Nat.le_trans hdl (Nat.le_mul_of_pos_left n (by norm_num only : 0 < 4))
    · rw [show D = 4 * d by
          dsimp only [D]
          exact positiveFundamentalDiscriminant_eq_four_mul hdmod]
      exact Nat.mul_le_mul_left 4 hdl
  let χ := primitiveQuadraticCharacter n hn
  have hχprim : χ.IsPrimitive :=
    DirichletCharacter.primitiveCharacter_isPrimitive (complexQuadraticCharacter n hn)
  have hχquad : χ.IsQuadratic := by
    let _ : NeZero (4 * n) := ⟨Nat.mul_ne_zero (by norm_num only) (Odd.pos hn).ne'⟩
    exact
      isQuadratic_primitiveCharacter (complexQuadraticCharacter n hn)
        (complexQuadraticCharacter_isQuadratic n hn)
  have hχeven : χ.Even := by exact primitiveQuadraticCharacter_isEven n hn
  have hχne : χ ≠ 1 := by exact primitiveQuadraticCharacter_ne_one_of_not_square n hn hns
  refine
    ⟨{  squarefreePart := d
        squareFactor := b
        squarefreePart_sq_mul := hfactor
        squarefreePart_pos := hdpos
        squarefreePart_gt_one := hdgt
        squarefreePart_odd := hdodd
        squarefreePart_squarefree := hdsquarefree
        discriminant := D
        discriminant_eq := rfl
        discriminant_isFundamentalDiscr := by
          dsimp only [D]
          exact positiveFundamentalDiscriminant_isFundamentalDiscr hdodd hdsquarefree
        discriminant_pos := hDpos
        discriminant_le := hDle
        character := χ
        character_eq := rfl
        character_primitive := hχprim
        character_quadratic := hχquad
        character_even := hχeven
        character_ne_one := hχne }, rfl, rfl⟩

end PseudoPrime.NumberTheory
