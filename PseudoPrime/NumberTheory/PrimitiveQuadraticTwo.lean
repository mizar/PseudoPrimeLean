/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.PrimitiveSquarefreeCharacter

/-! # Exact primitive quadratic values and conductor costs at two -/

@[expose] public section

namespace PseudoPrime.NumberTheory
/-- When the squarefree part is one modulo four, the primitive value at two
is its Jacobi numerator value. Evaluate at the odd unit d+2, reduce modulo the
exact conductor d, and transfer through the squarefree primitive character. -/
private theorem primitiveQuadratic_two_eq_jacobi {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (b : JacobiCharacterArithmeticData n hn hns)
    (h4 : b.squarefreePart % 4 = 1) :
    primitiveQuadraticCharacter n hn 2 = (jacobiSym 2 b.squarefreePart : ℂ) := by
  let : NeZero (4 * n) := ⟨mul_ne_zero (by norm_num only) hn.pos.ne'⟩
  have hdvd : b.squarefreePart ∣ n :=
    ⟨b.squareFactor ^ 2,by simpa only [mul_comm] using b.squarefreePart_sq_mul.symm⟩
  have hf := complexQuadraticCharacter_conductor_eq_squarefreePart_of_mod_four_eq_one
    b hdvd h4
  have he : ((b.squarefreePart + 2 : ℕ) :
      ZMod (complexQuadraticCharacter n hn).conductor) = 2 := by
    rw [hf,Nat.cast_add,ZMod.natCast_self,zero_add]
    rfl
  have ho : Odd (b.squarefreePart + 2) := b.squarefreePart_odd.add_even (by norm_num only)
  have hc : Nat.Coprime (b.squarefreePart + 2) (4 * b.squarefreePart) := by
    apply Nat.Coprime.mul_right
    · have hh := ho.coprime_two_right.pow_right 2
      norm_num only at hh
      exact hh
    · exact Nat.coprime_self_add_left.mpr b.squarefreePart_odd.coprime_two_left
  have hp := DirichletCharacter.primitiveCharacter_apply_of_isCoprime
    (complexQuadraticCharacter b.squarefreePart b.squarefreePart_odd) hc.isCoprime
  have hj : jacobiSym (b.squarefreePart + 2 : ℕ) b.squarefreePart =
      jacobiSym 2 b.squarefreePart := by
    apply jacobiSym.mod_left'
    rw [Nat.cast_add]
    simp only [Int.add_emod,Int.emod_self,zero_add,Int.emod_emod,Nat.cast_ofNat]
  calc
    _ = primitiveQuadraticCharacter n hn (b.squarefreePart + 2 : ℕ) :=
      (congrArg (primitiveQuadraticCharacter n hn) he).symm
    _ = primitiveQuadraticCharacter b.squarefreePart b.squarefreePart_odd
        (b.squarefreePart + 2 : ℕ) := by
      simpa only [Int.cast_natCast] using
        primitiveQuadraticCharacter_eq_squarefree_apply b (b.squarefreePart + 2 : ℕ)
    _ = complexQuadraticCharacter b.squarefreePart b.squarefreePart_odd
        (b.squarefreePart + 2 : ℕ) := by
      simpa only [primitiveQuadraticCharacter,Int.cast_natCast] using hp
    _ = _ := by
      have hq := quadraticCharacter_apply_of_coprime b.squarefreePart b.squarefreePart_odd hc
      simp only [Int.cast_natCast] at hq
      rw [complexQuadraticCharacter_apply,hq,ite_eq_left h4,hj]

/-- When the squarefree part is three modulo four, the exact conductor is 4d.
Two is a nonunit at that conductor, so the primitive character vanishes there.
This identifies the single log(2) exclusion cost in the ramified branch. -/
theorem primitiveQuadratic_two_zero {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (b : JacobiCharacterArithmeticData n hn hns)
    (h4 : b.squarefreePart % 4 = 3) :
    primitiveQuadraticCharacter n hn 2 = 0 := by
  let : NeZero (4 * n) := ⟨mul_ne_zero (by norm_num only) hn.pos.ne'⟩
  have hdvd : b.squarefreePart ∣ n :=
    ⟨b.squareFactor ^ 2,by simpa only [mul_comm] using b.squarefreePart_sq_mul.symm⟩
  have hf :=
    complexQuadraticCharacter_conductor_eq_four_mul_squarefreePart_of_mod_four_eq_three
      b hdvd h4
  apply MulChar.map_nonunit
  intro hu
  have hc := (ZMod.isUnit_iff_coprime 2 (complexQuadraticCharacter n hn).conductor).mp hu
  exact (Nat.prime_two.coprime_iff_not_dvd.mp hc)
    (hf.symm ▸ dvd_mul_of_dvd_left (by norm_num only : 2 ∣ 4) b.squarefreePart)
/-- For squarefree part one modulo eight, the primitive value at two is one.
Use its Jacobi evaluation and the supplementary law at two.
The odd-prime exclusion therefore charges zero at two. -/
theorem primitiveQuadratic_two_one {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (b : JacobiCharacterArithmeticData n hn hns)
    (h8 : b.squarefreePart % 8 = 1) :
    primitiveQuadraticCharacter n hn 2 = 1 := by
  have h4 : b.squarefreePart % 4 = 1 := by
    rw [← Nat.mod_mod_of_dvd b.squarefreePart (by norm_num only : 4 ∣ 8),h8]
  rw [primitiveQuadratic_two_eq_jacobi b h4,jacobiSym.at_two b.squarefreePart_odd,
    ZMod.χ₈_nat_eq_if_mod_eight,h8]
  norm_num only [Nat.odd_iff.mp b.squarefreePart_odd,ite_true,ite_false,or_false]
/-- For squarefree part five modulo eight, the primitive value at two is minus one.
Use the Jacobi evaluation and the supplementary law at two.
The odd-prime restriction retains a cost of twice log(2) despite conductor d. -/
theorem primitiveQuadratic_two_neg_one {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (b : JacobiCharacterArithmeticData n hn hns)
    (h8 : b.squarefreePart % 8 = 5) :
    primitiveQuadraticCharacter n hn 2 = -1 := by
  have h4 : b.squarefreePart % 4 = 1 := by
    rw [← Nat.mod_mod_of_dvd b.squarefreePart (by norm_num only : 4 ∣ 8),h8]
  rw [primitiveQuadratic_two_eq_jacobi b h4,jacobiSym.at_two b.squarefreePart_odd,
    ZMod.χ₈_nat_eq_if_mod_eight,h8]
  norm_num only [Nat.odd_iff.mp b.squarefreePart_odd,ite_true,ite_false,or_false]
/-- Under the stated residue condition on the canonical squarefree part, identify
both the exact primitive conductor and the exact logarithmic cost at two.
Combine the existing conductor theorem with the proved primitive value;
these data feed the cubic exclusion radius without uniformizing the branches. -/
theorem quadratic_mod_eight_one_data {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (b : JacobiCharacterArithmeticData n hn hns) (h8 : b.squarefreePart % 8 = 1) :
    (complexQuadraticCharacter n hn).conductor = b.squarefreePart ∧
      (1-(primitiveQuadraticCharacter n hn 2).re) * Real.log 2 = 0 := by
  let : NeZero (4 * n) := ⟨mul_ne_zero (by norm_num only) hn.pos.ne'⟩
  have hdvd : b.squarefreePart ∣ n :=
    ⟨b.squareFactor ^ 2,by simpa only [mul_comm] using b.squarefreePart_sq_mul.symm⟩
  have h4 : b.squarefreePart % 4 = 1 := by
    rw [← Nat.mod_mod_of_dvd b.squarefreePart (by norm_num only : 4 ∣ 8),h8]
  refine ⟨complexQuadraticCharacter_conductor_eq_squarefreePart_of_mod_four_eq_one
    b hdvd h4,?_⟩
  rw [primitiveQuadratic_two_one b h8]
  norm_num only [Complex.one_re,Complex.neg_re,Complex.zero_re,zero_mul,one_mul]
/-- Under the stated residue condition on the canonical squarefree part, identify
both the exact primitive conductor and the exact logarithmic cost at two.
Combine the existing conductor theorem with the proved primitive value;
these data feed the cubic exclusion radius without uniformizing the branches. -/
theorem quadratic_mod_eight_five_data {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (b : JacobiCharacterArithmeticData n hn hns) (h8 : b.squarefreePart % 8 = 5) :
    (complexQuadraticCharacter n hn).conductor = b.squarefreePart ∧
      (1-(primitiveQuadraticCharacter n hn 2).re) * Real.log 2 = 2 * Real.log 2 := by
  let : NeZero (4 * n) := ⟨mul_ne_zero (by norm_num only) hn.pos.ne'⟩
  have hdvd : b.squarefreePart ∣ n :=
    ⟨b.squareFactor ^ 2,by simpa only [mul_comm] using b.squarefreePart_sq_mul.symm⟩
  have h4 : b.squarefreePart % 4 = 1 := by
    rw [← Nat.mod_mod_of_dvd b.squarefreePart (by norm_num only : 4 ∣ 8),h8]
  refine ⟨complexQuadraticCharacter_conductor_eq_squarefreePart_of_mod_four_eq_one
    b hdvd h4,?_⟩
  rw [primitiveQuadratic_two_neg_one b h8]
  norm_num only [Complex.one_re,Complex.neg_re,Complex.zero_re,zero_mul,one_mul]
/-- Under the stated residue condition on the canonical squarefree part, identify
both the exact primitive conductor and the exact logarithmic cost at two.
Combine the existing conductor theorem with the proved primitive value;
these data feed the cubic exclusion radius without uniformizing the branches. -/
theorem quadratic_mod_eight_three_seven {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (b : JacobiCharacterArithmeticData n hn hns)
    (h8 : b.squarefreePart % 8 = 3 ∨ b.squarefreePart % 8 = 7) :
    (complexQuadraticCharacter n hn).conductor = 4 * b.squarefreePart ∧
      (1-(primitiveQuadraticCharacter n hn 2).re) * Real.log 2 = Real.log 2 := by
  let : NeZero (4 * n) := ⟨mul_ne_zero (by norm_num only) hn.pos.ne'⟩
  have hdvd : b.squarefreePart ∣ n :=
    ⟨b.squareFactor ^ 2,by simpa only [mul_comm] using b.squarefreePart_sq_mul.symm⟩
  have h4 : b.squarefreePart % 4 = 3 := by
    rw [← Nat.mod_mod_of_dvd b.squarefreePart (by norm_num only : 4 ∣ 8)]
    rcases h8 with h8 | h8 <;> rw [h8]
  refine ⟨complexQuadraticCharacter_conductor_eq_four_mul_squarefreePart_of_mod_four_eq_three
    b hdvd h4,?_⟩
  rw [primitiveQuadratic_two_zero b h4]
  norm_num only [Complex.one_re,Complex.neg_re,Complex.zero_re,zero_mul,one_mul]
end PseudoPrime.NumberTheory
