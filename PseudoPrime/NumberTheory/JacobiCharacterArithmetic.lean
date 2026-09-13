/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.NumberTheory.DirichletCharacter
import PseudoPrime.NumberTheory.JacobiCongruence
import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.LSeries.PrimesInAP
import PseudoPrime.NumberTheory.PrimitiveJacobiCharacter
import PseudoPrime.NumberTheory.Jacobi.Numerator
import Mathlib.NumberTheory.FundamentalDiscriminant

/-!
# Arithmetic of Jacobi characters and their primitive conductors

This file packages the squarefree-part decomposition used before the analytic argument.  The
primitive character is the existing canonical character induced by the quadratic character of
`n`; the positive discriminant certificate records the elementary bound `D ≤ 4 * n`.
Conductor identities and transfer of Jacobi witnesses depend only on this arithmetic data.
-/

namespace PseudoPrime.NumberTheory

/--
The arithmetic and character data supplied by an odd nonsquare input `n`.
`squarefreePart` and `squareFactor` give `n = squareFactor² * squarefreePart`; the accompanying
fields certify positivity, oddness, squarefreeness, and `squarefreePart > 1`.
`discriminant` is its positive fundamental discriminant, with positivity and `discriminant ≤ 4*n`.
`character` is the canonical primitive character induced from `complexQuadraticCharacter n hn`;
its fields record that identity, primitivity, quadratic values, even parity, and nontriviality.
This package supplies conductor identities and witness-transfer theorems without analytic
assumptions.
-/
structure JacobiCharacterArithmeticData (n : ℕ) (hn : Odd n) (hns : ¬IsSquare n) where
  squarefreePart : ℕ
  squareFactor : ℕ
  squarefreePart_sq_mul : squareFactor ^ 2 * squarefreePart = n
  squarefreePart_pos : 0 < squarefreePart
  squarefreePart_gt_one : 1 < squarefreePart
  squarefreePart_odd : Odd squarefreePart
  squarefreePart_squarefree : Squarefree squarefreePart
  discriminant : ℕ
  discriminant_eq :
    discriminant = positiveFundamentalDiscriminant squarefreePart
  discriminant_isFundamentalDiscr : (discriminant : ℤ).IsFundamentalDiscr
  discriminant_pos : 0 < discriminant
  discriminant_le : discriminant ≤ 4 * n
  character :
    DirichletCharacter ℂ (complexQuadraticCharacter n hn).conductor
  character_eq : character = primitiveQuadraticCharacter n hn
  character_primitive : character.IsPrimitive
  character_quadratic : character.IsQuadratic
  character_even : character.Even
  character_ne_one : character ≠ 1

/-- The primitive conductor always divides the original level `4 * n`. -/
theorem primitiveQuadraticCharacter_conductor_dvd_level (n : ℕ) (hn : Odd n) :
    (primitiveQuadraticCharacter n hn).conductor ∣ 4 * n := by
  have hconductor :
    (primitiveQuadraticCharacter n hn).conductor =
      (complexQuadraticCharacter n hn).conductor :=
    (DirichletCharacter.isPrimitive_def
          (primitiveQuadraticCharacter n hn)).mp
      (primitiveQuadraticCharacter_isPrimitive n hn)
  rw [hconductor]
  exact
    DirichletCharacter.conductor_dvd_level (complexQuadraticCharacter n hn)

/-- The primitive conductor is bounded by the original level `4 * n`. -/
theorem primitiveQuadraticCharacter_conductor_le_level (n : ℕ) (hn : Odd n) :
    (primitiveQuadraticCharacter n hn).conductor ≤ 4 * n := by
  have hnpos : 0 < n := Odd.pos hn
  exact
    Nat.le_of_dvd (by positivity)
      (primitiveQuadraticCharacter_conductor_dvd_level n hn)

/-- At a denominator coprime to `n`, the square factor in `n=b²*d` is invisible to the Jacobi
value.
-/
theorem jacobiSym_eq_squarefreePart_of_coprime {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : JacobiCharacterArithmeticData n hn hns) {p : ℕ}
    (hcop : Nat.Coprime n p) : jacobiSym n p = jacobiSym bridge.squarefreePart p := by
  have hddiv : bridge.squarefreePart ∣ n := by
    refine ⟨bridge.squareFactor ^ 2, ?_⟩
    simpa only [mul_comm] using bridge.squarefreePart_sq_mul.symm
  have hdcop : Nat.Coprime bridge.squarefreePart p := hcop.of_dvd_left hddiv
  have hfactorInt : (n : ℤ) = (bridge.squareFactor : ℤ) ^ 2 * bridge.squarefreePart := by
    exact_mod_cast bridge.squarefreePart_sq_mul.symm
  rw [hfactorInt, jacobiSym.mul_left, jacobiSym.pow_left]
  have hbcop : Nat.Coprime bridge.squareFactor p := by
    apply hcop.of_dvd_left
    refine ⟨bridge.squareFactor * bridge.squarefreePart, ?_⟩
    calc
      n = bridge.squareFactor ^ 2 * bridge.squarefreePart := bridge.squarefreePart_sq_mul.symm
      _ = bridge.squareFactor * (bridge.squareFactor * bridge.squarefreePart) := by ring
  have hsq : jacobiSym (bridge.squareFactor : ℤ) p ^ 2 = 1 := by
    apply jacobiSym.sq_one
    simpa only [Int.gcd_natCast_natCast] using hbcop.gcd_eq_one
  rw [hsq, one_mul]

/-- In the denominator, the square factor in `n=b²*d` is invisible to a coprime Jacobi value. -/
theorem jacobiSym_eq_squarefreePart_denominator_of_coprime {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : JacobiCharacterArithmeticData n hn hns) {a : ℕ}
    (hcop : Nat.Coprime a n) : jacobiSym a n = jacobiSym a bridge.squarefreePart := by
  have hbpos : 0 < bridge.squareFactor := by
    by_contra hb
    have hbzero : bridge.squareFactor = 0 := Nat.eq_zero_of_not_pos hb
    have hnzero : n = 0 := by
      rw [← bridge.squarefreePart_sq_mul, hbzero]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]
    exact (Odd.pos hn).ne' hnzero
  let _ : NeZero bridge.squareFactor := ⟨Nat.ne_of_gt hbpos⟩
  let _ : NeZero bridge.squarefreePart := ⟨Nat.ne_of_gt bridge.squarefreePart_pos⟩
  have hbdiv : bridge.squareFactor ∣ n := by
    refine ⟨bridge.squareFactor * bridge.squarefreePart, ?_⟩
    calc
      n = bridge.squareFactor ^ 2 * bridge.squarefreePart := bridge.squarefreePart_sq_mul.symm
      _ = bridge.squareFactor * (bridge.squareFactor * bridge.squarefreePart) := by ring
  have hbcop : Nat.Coprime a bridge.squareFactor := hcop.of_dvd_right hbdiv
  calc
    jacobiSym a n = jacobiSym a (bridge.squareFactor ^ 2 * bridge.squarefreePart) := by
      rw [bridge.squarefreePart_sq_mul]
    _ = jacobiSym a (bridge.squareFactor ^ 2) * jacobiSym a bridge.squarefreePart := by
      rw [jacobiSym.mul_right]
    _ = jacobiSym a bridge.squarefreePart := by
      have hsq : jacobiSym a (bridge.squareFactor ^ 2) = 1 := by
        rw [jacobiSym.pow_right]
        have hsq' : jacobiSym (a : ℤ) bridge.squareFactor ^ 2 = 1 := by
          apply jacobiSym.sq_one
          simpa only [Int.gcd_natCast_natCast] using hbcop.gcd_eq_one
        exact_mod_cast hsq'
      rw [hsq, one_mul]

/-- Construct the complete squarefree/discriminant/character bridge for an odd nonsquare. -/
theorem exists_jacobiCharacterArithmeticData {n : ℕ} (hnpos : 0 < n) (hn : Odd n)
    (hns : ¬IsSquare n) :
    Nonempty (JacobiCharacterArithmeticData n hn hns) := by
  obtain ⟨d, b, hdpos, hbpos, hfactor, hdsquarefree⟩ := Nat.sq_mul_squarefree_of_pos hnpos
  have hdgt : 1 < d := by
    have hdne : d ≠ 1 := by
      intro hd
      apply hns
      refine ⟨b, ?_⟩
      rw [← hfactor, hd]
      simp only [pow_two, mul_one]
    omega
  have hdodd : Odd d := by
    by_contra hdnot
    have hdeven : Even d := Nat.not_odd_iff_even.mp hdnot
    obtain ⟨k, hk⟩ := hdeven
    apply (Nat.not_even_iff_odd.mpr hn)
    refine ⟨b ^ 2 * k, ?_⟩
    rw [← hfactor, hk]
    ring
  let D := positiveFundamentalDiscriminant d
  have hDpos : 0 < D := by
    by_cases hdmod : d % 4 = 1
    · rw [show D = d by
          dsimp [D]
          exact positiveFundamentalDiscriminant_eq_self hdmod]
      exact hdpos
    · rw [show D = 4 * d by
          dsimp [D]
          exact positiveFundamentalDiscriminant_eq_four_mul hdmod]
      positivity
  have hdl : d ≤ n := by
    rw [← hfactor]
    have hb1 : 1 ≤ b := by omega
    have hbpow : 1 ≤ b ^ 2 := one_le_pow₀ hb1
    simpa only [Nat.mul_comm, ge_iff_le] using Nat.le_mul_of_pos_right d hbpow
  have hDle : D ≤ 4 * n := by
    by_cases hdmod : d % 4 = 1
    · rw [show D = d by
          dsimp [D]
          exact positiveFundamentalDiscriminant_eq_self hdmod]
      omega
    · rw [show D = 4 * d by
          dsimp [D]
          exact positiveFundamentalDiscriminant_eq_four_mul hdmod]
      exact Nat.mul_le_mul_left 4 hdl
  let χ := primitiveQuadraticCharacter n hn
  have hχprim : χ.IsPrimitive := by
    exact primitiveQuadraticCharacter_isPrimitive n hn
  have hχquad : χ.IsQuadratic := by
    exact primitiveQuadraticCharacter_isQuadratic n hn
  have hχeven : χ.Even := by exact primitiveQuadraticCharacter_isEven n hn
  have hχne : χ ≠ 1 := by
    exact primitiveQuadraticCharacter_ne_one_of_not_square n hn hns
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
          dsimp [D]
          exact
            positiveFundamentalDiscriminant_isFundamentalDiscr hdodd
              hdsquarefree
        discriminant_pos := hDpos
        discriminant_le := hDle
        character := χ
        character_eq := rfl
        character_primitive := hχprim
        character_quadratic := hχquad
        character_even := hχeven
        character_ne_one := hχne }⟩

/-- The bridge discriminant is bounded by `n` whenever its odd branch is selected. -/
theorem JacobiCharacterArithmeticData.discriminant_le_of_mod_four_eq_one {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} (bridge : JacobiCharacterArithmeticData n hn hns)
    (hdmod : bridge.squarefreePart % 4 = 1) : bridge.discriminant ≤ n := by
  calc
    bridge.discriminant =
        positiveFundamentalDiscriminant bridge.squarefreePart :=
      bridge.discriminant_eq
    _ = bridge.squarefreePart :=
      positiveFundamentalDiscriminant_eq_self hdmod
    _ ≤ bridge.squareFactor ^ 2 * bridge.squarefreePart := by
      apply le_mul_of_one_le_left'
      have hbpos : 0 < bridge.squareFactor := by
        by_contra hb
        have hbzero : bridge.squareFactor = 0 := Nat.eq_zero_of_not_pos hb
        have hnzero : n = 0 := by
          rw [← bridge.squarefreePart_sq_mul, hbzero]
          simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]
        exact (Odd.pos hn).ne' hnzero
      exact Nat.one_le_pow 2 bridge.squareFactor hbpos
    _ = n := bridge.squarefreePart_sq_mul

/-- The square factor in the odd squarefree decomposition is odd. -/
theorem JacobiCharacterArithmeticData.squareFactor_odd {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : JacobiCharacterArithmeticData n hn hns) :
    Odd bridge.squareFactor := by
  have hprod : Odd (bridge.squareFactor ^ 2 * bridge.squarefreePart) := by
    rw [bridge.squarefreePart_sq_mul]
    exact hn
  have hbsq : Odd (bridge.squareFactor ^ 2) := (Nat.odd_mul.mp hprod).1
  have hbm : Odd (bridge.squareFactor * bridge.squareFactor) := by simpa only [pow_two] using hbsq
  exact (Nat.odd_mul.mp hbm).1

/-- The input and its odd squarefree part have the same residue modulo `4`. -/
theorem JacobiCharacterArithmeticData.input_mod_four_eq_squarefreePart_mod_four {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} (bridge : JacobiCharacterArithmeticData n hn hns) :
    n % 4 = bridge.squarefreePart % 4 := by
  have hbmod : bridge.squareFactor ^ 2 % 4 = 1 := by
    have hmod : bridge.squareFactor % 4 = 1 ∨ bridge.squareFactor % 4 = 3 :=
      Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp bridge.squareFactor_odd)
    rcases hmod with h | h
    · have hm : Nat.ModEq 4 bridge.squareFactor 1 := h
      simpa only [Nat.ModEq, one_pow, Nat.one_mod] using Nat.ModEq.pow 2 hm
    · have hm : Nat.ModEq 4 bridge.squareFactor 3 := h
      simpa only [Nat.ModEq, Nat.reducePow, Nat.reduceMod] using Nat.ModEq.pow 2 hm
  calc
    n % 4 = (bridge.squareFactor ^ 2 * bridge.squarefreePart) % 4 :=
      congrArg (fun x => x % 4) bridge.squarefreePart_sq_mul.symm
    _ = (bridge.squareFactor ^ 2 % 4 * (bridge.squarefreePart % 4)) % 4 := by
      simp only [Nat.mul_mod, dvd_refl, Nat.mod_mod_of_dvd]
    _ = bridge.squarefreePart % 4 := by
      rw [hbmod]
      simp only [one_mul, dvd_refl, Nat.mod_mod_of_dvd]

/-- At a unit of the original level, the quadratic character can be evaluated using the odd
squarefree part. -/
theorem quadraticCharacter_apply_of_squarefreePart_coprime {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : JacobiCharacterArithmeticData n hn hns) {a : ℕ}
    (hcop : Nat.Coprime a (4 * n)) :
    quadraticCharacter n hn ((a : ℤ) : ZMod (4 * n)) =
      if bridge.squarefreePart % 4 = 1 then jacobiSym a bridge.squarefreePart
      else jacobiSym a bridge.squarefreePart * ZMod.χ₄ ((a : ℤ) : ZMod 4) := by
  have hdiv : n ∣ 4 * n := by
    rw [Nat.mul_comm]
    exact Nat.dvd_mul_right n 4
  have hcopn : Nat.Coprime a n := Nat.Coprime.of_dvd_right hdiv hcop
  have hj :=
    jacobiSym_eq_squarefreePart_denominator_of_coprime bridge hcopn
  have hmod := bridge.input_mod_four_eq_squarefreePart_mod_four
  rw [quadraticCharacter_apply_of_coprime n hn hcop]
  simp only [hmod, hj]

/-- On units, the character agrees with the character of the squarefree part raised to level
`4*n`. This holds for both odd residue classes of the squarefree part modulo `4`. -/
theorem quadraticCharacter_eq_squarefreePart_changeLevel_apply_of_coprime {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} (bridge : JacobiCharacterArithmeticData n hn hns)
    (hdvd : 4 * bridge.squarefreePart ∣ 4 * n) {a : ℕ} (hcop : Nat.Coprime a (4 * n)) :
    quadraticCharacter n hn ((a : ℤ) : ZMod (4 * n)) =
      DirichletCharacter.changeLevel hdvd
        (quadraticCharacter bridge.squarefreePart
          bridge.squarefreePart_odd)
        ((a : ℤ) : ZMod (4 * n)) := by
  have hcopd : Nat.Coprime a (4 * bridge.squarefreePart) := Nat.Coprime.of_dvd_right hdvd hcop
  rw [quadraticCharacter_apply_of_squarefreePart_coprime bridge hcop]
  rw [DirichletCharacter.changeLevel_eq_cast_of_dvd' _ hdvd (a := (a : ℤ))
      (Int.isCoprime_iff_nat_coprime.mpr hcop)]
  rw [quadraticCharacter_apply_of_coprime _ bridge.squarefreePart_odd
      hcopd]

/-- The comparison theorem supplies the factor-through kernel condition at level `4*d`. -/
theorem quadraticCharacter_factorsThrough_squarefreePart {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    [NeZero (4 * n)] (bridge : JacobiCharacterArithmeticData n hn hns)
    (hdvd : 4 * bridge.squarefreePart ∣ 4 * n) :
    DirichletCharacter.FactorsThrough (quadraticCharacter n hn)
      (4 * bridge.squarefreePart) := by
  refine (DirichletCharacter.factorsThrough_iff_ker_unitsMap hdvd).mpr ?_
  intro x hx
  rw [MonoidHom.mem_ker]
  let a : ℕ := (↑x : ZMod (4 * n)).val
  have hcop : Nat.Coprime a (4 * n) := ZMod.val_coe_unit_coprime x
  have hxeq : x = ZMod.unitOfCoprime a hcop := by
    apply Units.ext
    simp only [ZMod.unitOfCoprime, ZMod.natCast_val, ZMod.cast_id', id_eq, ZMod.inv_coe_unit,
      Units.mk_val, a]
  have hpoint :=
    quadraticCharacter_eq_squarefreePart_changeLevel_apply_of_coprime
      bridge hdvd hcop
  have hcandidate :
    DirichletCharacter.changeLevel hdvd
        (quadraticCharacter bridge.squarefreePart
          bridge.squarefreePart_odd)
        ((a : ℤ) : ZMod (4 * n)) =
      1 := by
    rw [DirichletCharacter.changeLevel_eq_cast_of_dvd' _ hdvd (a := (a : ℤ))
        (Int.isCoprime_iff_nat_coprime.mpr hcop)]
    have hunit : ZMod.unitsMap hdvd (ZMod.unitOfCoprime a hcop) = 1 := by
      rw [← hxeq]
      exact hx
    have hval :=
      congrArg
        (fun z : (ZMod (4 * bridge.squarefreePart))ˣ => (z : ZMod (4 * bridge.squarefreePart)))
        hunit
    have hcast : (a : ZMod (4 * bridge.squarefreePart)) = 1 := by
      have ha_lt : a < 4 * n := ZMod.val_lt (↑x : ZMod (4 * n))
      simpa only [ZMod.unitsMap_val, ZMod.coe_unitOfCoprime, ← ZMod.natCast_val, ZMod.val_natCast,
        Nat.mod_eq_of_lt ha_lt, Units.val_one] using hval
    have hcast' : ((a : ℤ) : ZMod (4 * bridge.squarefreePart)) = 1 := by
      simpa only [Int.cast_natCast] using hcast
    rw [hcast']
    simp only [map_one]
  apply Units.ext
  rw [MulChar.coe_toUnitHom, hxeq]
  have hdiv : n ∣ 4 * n := ⟨4, by simp only [Nat.mul_comm]⟩
  simpa only [Int.cast_natCast, ZMod.cast_natCast hdiv, ZMod.unitOfCoprime, ZMod.natCast_val,
    ZMod.cast_id', id_eq, ZMod.inv_coe_unit, Units.mk_val, Units.val_one, ZMod.intCast_cast] using
    hpoint.trans hcandidate

/-- In the `d = 1 mod 4` branch, the extra factor `4` also disappears. -/
theorem quadraticCharacter_factorsThrough_squarefreePart_of_mod_four_eq_one {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} [NeZero (4 * n)]
    (bridge : JacobiCharacterArithmeticData n hn hns)
    (hdvd : bridge.squarefreePart ∣ n) (hd4 : bridge.squarefreePart % 4 = 1) :
    DirichletCharacter.FactorsThrough (quadraticCharacter n hn)
      bridge.squarefreePart := by
  have hlevel : bridge.squarefreePart ∣ 4 * n := by
    exact
      dvd_trans hdvd
        (by
          rw [Nat.mul_comm]
          exact Nat.dvd_mul_right n 4)
  refine (DirichletCharacter.factorsThrough_iff_ker_unitsMap hlevel).mpr ?_
  intro x hx
  rw [MonoidHom.mem_ker]
  let a : ℕ := (↑x : ZMod (4 * n)).val
  have hcop : Nat.Coprime a (4 * n) := ZMod.val_coe_unit_coprime x
  have hxeq : x = ZMod.unitOfCoprime a hcop := by
    apply Units.ext
    simp only [ZMod.unitOfCoprime, ZMod.natCast_val, ZMod.cast_id', id_eq, ZMod.inv_coe_unit,
      Units.mk_val, a]
  have hunit : ZMod.unitsMap hlevel (ZMod.unitOfCoprime a hcop) = 1 := by
    rw [← hxeq]
    exact hx
  have hval :=
    congrArg (fun z : (ZMod bridge.squarefreePart)ˣ => (z : ZMod bridge.squarefreePart)) hunit
  have hcast : (a : ZMod bridge.squarefreePart) = 1 := by
    have ha_lt : a < 4 * n := ZMod.val_lt (↑x : ZMod (4 * n))
    simpa only [ZMod.unitsMap_val, ZMod.coe_unitOfCoprime, ← ZMod.natCast_val, ZMod.val_natCast,
      Nat.mod_eq_of_lt ha_lt, Units.val_one] using hval
  have hj : jacobiSym a bridge.squarefreePart = 1 := by
    have hv := congrArg ZMod.val hcast
    rw [ZMod.val_natCast, ZMod.val_one_eq_one_mod] at hv
    have hj' :
      jacobiSym (a : ℤ) bridge.squarefreePart = jacobiSym (1 : ℤ) bridge.squarefreePart := by
      apply jacobiSym.mod_left'
      exact_mod_cast hv
    simpa only [jacobiSym.one_left] using hj'
  have hpoint :=
    quadraticCharacter_apply_of_squarefreePart_coprime bridge hcop
  simp only [ite_eq_left hd4] at hpoint
  apply Units.ext
  rw [MulChar.coe_toUnitHom, hxeq]
  have hdiv : n ∣ 4 * n := ⟨4, by simp only [Nat.mul_comm]⟩
  simpa only [Int.cast_natCast, ZMod.cast_natCast hdiv, ZMod.unitOfCoprime, ZMod.natCast_val,
    ZMod.cast_id', id_eq, ZMod.inv_coe_unit, Units.mk_val, Units.val_one, ZMod.intCast_cast] using
    hpoint.trans hj

/-- In the `d = 1 mod 4` branch, the quadratic character conductor divides `d`. -/
theorem quadraticCharacter_conductor_dvd_squarefreePart_of_mod_four_eq_one {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} [NeZero (4 * n)]
    (bridge : JacobiCharacterArithmeticData n hn hns)
    (hdvd : bridge.squarefreePart ∣ n) (hd4 : bridge.squarefreePart % 4 = 1) :
    (quadraticCharacter n hn).conductor ∣ bridge.squarefreePart := by
  apply DirichletCharacter.conductor_dvd_of_mem_conductorSet
  exact
    (DirichletCharacter.mem_conductorSet_iff _).mpr
      (quadraticCharacter_factorsThrough_squarefreePart_of_mod_four_eq_one
        bridge hdvd hd4)

/-- For either odd residue class of the squarefree part `d`, the conductor divides `4*d`. -/
theorem quadraticCharacter_conductor_dvd_four_mul_squarefreePart {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} [NeZero (4 * n)]
    (bridge : JacobiCharacterArithmeticData n hn hns)
    (hdvd : bridge.squarefreePart ∣ n) :
    (quadraticCharacter n hn).conductor ∣ 4 * bridge.squarefreePart := by
  apply DirichletCharacter.conductor_dvd_of_mem_conductorSet
  exact
    (DirichletCharacter.mem_conductorSet_iff _).mpr
      (quadraticCharacter_factorsThrough_squarefreePart bridge
        (Nat.mul_dvd_mul_left 4 hdvd))

/-- The `d` and `2*d` proper divisors are excluded in the `d = 3 mod 4` branch by
the nontrivial value of `χ₄`. -/
theorem complexQuadraticCharacter_not_factorsThrough_eq_d_or_two_mul {d c : ℕ} {hdodd : Odd d}
    (hd4 : d % 4 = 3) (hc : c = d ∨ c = 2 * d) :
    ¬DirichletCharacter.FactorsThrough (complexQuadraticCharacter d hdodd)
        c := by
  intro hfactor
  obtain ⟨a, haodd, hac, haj, ha4, _⟩ :=
    exists_nat_odd_one_modEq_and_jacobiSym_eq_one_of_eq_d_or_two_mul hdodd
      hd4 (by omega : 0 < 1) hc
  have hacopd : Nat.Coprime a d := by
    rw [Nat.coprime_iff_gcd_eq_one]
    by_contra hne
    have hz : jacobiSym (a : ℤ) d = 0 := by
      apply (jacobiSym.eq_zero_iff).mpr
      exact ⟨(Odd.pos hdodd).ne', by simpa only [Int.gcd_natCast_natCast, ne_eq] using hne⟩
    rw [hz] at haj
    norm_num only at haj
  have hacop4 : Nat.Coprime a 4 := by
    simpa only [pow_two] using Nat.Coprime.mul_right haodd.coprime_two_right haodd.coprime_two_right
  have hacop : Nat.Coprime a (4 * d) := hacop4.mul_right hacopd
  have hone := factorsThrough_apply_eq_one_of_one_modEq hfactor hac hacop
  have hq := quadraticCharacter_apply_of_coprime d hdodd hacop
  simp only [ite_eq_right (by omega : ¬d % 4 = 1)] at hq
  have ha4int : (a : ℤ) % 4 = (3 : ℤ) % 4 := by exact_mod_cast ha4
  have hchi : ZMod.χ₄ ((a : ℤ) : ZMod 4) = -1 := by exact ZMod.χ₄_int_three_mod_four ha4int
  rw [haj, hchi] at hq
  have hval :=
    complexQuadraticCharacter_apply d hdodd ((a : ℤ) : ZMod (4 * d))
  have hone' :
    ((quadraticCharacter d hdodd) ((a : ℤ) : ZMod (4 * d)) : ℂ) = 1 := by
    rw [← hval]
    exact hone
  rw [hq] at hone'
  norm_num only at hone'

/-- The 2-adic proper-divisor obstruction also applies to the original level `n=b²*d`; the
prime-AP representative is chosen above the square factor and is therefore a unit at `4*n`. -/
theorem complexQuadraticCharacter_not_factorsThrough_eq_d_or_two_mul_of_bridge {n c : ℕ}
    {hn : Odd n} {hns : ¬IsSquare n} [NeZero (4 * n)]
    (bridge : JacobiCharacterArithmeticData n hn hns)
    (hd4 : bridge.squarefreePart % 4 = 3)
    (hc : c = bridge.squarefreePart ∨ c = 2 * bridge.squarefreePart) :
    ¬DirichletCharacter.FactorsThrough (complexQuadraticCharacter n hn)
        c := by
  intro hfactor
  obtain ⟨a, haodd, hac, haj, ha4, has⟩ :=
    exists_nat_odd_one_modEq_and_jacobiSym_eq_one_of_eq_d_or_two_mul
      bridge.squarefreePart_odd hd4 (Odd.pos bridge.squareFactor_odd) hc
  have hacopd : Nat.Coprime a bridge.squarefreePart := by
    rw [Nat.coprime_iff_gcd_eq_one]
    by_contra hne
    have hz : jacobiSym (a : ℤ) bridge.squarefreePart = 0 := by
      apply (jacobiSym.eq_zero_iff).mpr
      exact
        ⟨bridge.squarefreePart_pos.ne', by simpa only [Int.gcd_natCast_natCast, ne_eq] using hne⟩
    rw [hz] at haj
    norm_num only at haj
  have hacopn : Nat.Coprime a n := by
    rw [← bridge.squarefreePart_sq_mul]
    simpa only [pow_two] using (Nat.Coprime.mul_right has has).mul_right hacopd
  have hacop4 : Nat.Coprime a 4 := by
    simpa only [pow_two] using Nat.Coprime.mul_right haodd.coprime_two_right haodd.coprime_two_right
  have hacop : Nat.Coprime a (4 * n) := hacop4.mul_right hacopn
  have hone := factorsThrough_apply_eq_one_of_one_modEq hfactor hac hacop
  have hq :=
    quadraticCharacter_apply_of_squarefreePart_coprime bridge hacop
  simp only [ite_eq_right (by omega : ¬bridge.squarefreePart % 4 = 1)] at hq
  have ha4int : (a : ℤ) % 4 = (3 : ℤ) % 4 := by exact_mod_cast ha4
  have hchi : ZMod.χ₄ ((a : ℤ) : ZMod 4) = -1 := ZMod.χ₄_int_three_mod_four ha4int
  rw [haj, hchi] at hq
  have hval :=
    complexQuadraticCharacter_apply n hn ((a : ℤ) : ZMod (4 * n))
  have hone' :
    ((quadraticCharacter n hn) ((a : ℤ) : ZMod (4 * n)) : ℂ) = 1 := by
    rw [← hval]
    exact hone
  rw [hq] at hone'
  norm_num only at hone'

/-- In the `d = 1 mod 4` branch, the quadratic character cannot factor through a
proper divisor of the squarefree modulus. -/
theorem quadraticCharacter_not_factorsThrough_proper_divisor_of_mod_four_eq_one {d c : ℕ}
    {hdodd : Odd d} [NeZero (4 * d)] (hdsq : Squarefree d) (hd4 : d % 4 = 1) (hc : c ∣ d)
    (hnot : ¬d ∣ c) :
    ¬DirichletCharacter.FactorsThrough (quadraticCharacter d hdodd) c := by
  intro hfactor
  obtain ⟨a, haodd, hac, haj⟩ :=
    exists_nat_odd_one_modEq_and_jacobiSym_eq_neg_one hdodd hdsq hc hnot
  have hacopd : Nat.Coprime a d := by
    rw [Nat.coprime_iff_gcd_eq_one]
    by_contra hne
    have hz : jacobiSym (a : ℤ) d = 0 := by
      apply (jacobiSym.eq_zero_iff).mpr
      exact ⟨(Odd.pos hdodd).ne', by simpa only [Int.gcd_natCast_natCast, ne_eq] using hne⟩
    rw [hz] at haj
    norm_num only at haj
  have hacop4 : Nat.Coprime a 4 := by
    simpa only [pow_two] using Nat.Coprime.mul_right haodd.coprime_two_right haodd.coprime_two_right
  have hacop : Nat.Coprime a (4 * d) := hacop4.mul_right hacopd
  have hone := factorsThrough_apply_eq_one_of_one_modEq hfactor hac hacop
  have hval := quadraticCharacter_apply_of_coprime d hdodd hacop
  simp only [ite_eq_left hd4] at hval
  rw [haj] at hval
  rw [hval] at hone
  norm_num only at hone

/-- In the `d = 3 mod 4` branch, any proper divisor missing an odd factor is also
excluded at the full level `4*d`; the CRT representative fixes the `χ₄` value to `1`. -/
theorem complexQuadraticCharacter_not_factorsThrough_proper_divisor_of_mod_four_eq_three {d c : ℕ}
    {hdodd : Odd d} (hdsq : Squarefree d) (hd4 : d % 4 = 3) (hc : c ∣ 4 * d) (hdnot : ¬d ∣ c) :
    ¬DirichletCharacter.FactorsThrough (complexQuadraticCharacter d hdodd)
        c := by
  intro hfactor
  obtain ⟨a, haodd, ha4, hac, haj⟩ :=
    exists_nat_odd_one_modEq_and_jacobiSym_eq_neg_one_of_dvd_four_mul hdodd
      hdsq hc hdnot
  have hacopd : Nat.Coprime a d := by
    rw [Nat.coprime_iff_gcd_eq_one]
    by_contra hne
    have hz : jacobiSym (a : ℤ) d = 0 := by
      apply (jacobiSym.eq_zero_iff).mpr
      exact ⟨(Odd.pos hdodd).ne', by simpa only [Int.gcd_natCast_natCast, ne_eq] using hne⟩
    rw [hz] at haj
    norm_num only at haj
  have hacop4 : Nat.Coprime a 4 := by
    simpa only [pow_two] using Nat.Coprime.mul_right haodd.coprime_two_right haodd.coprime_two_right
  have hacop : Nat.Coprime a (4 * d) := hacop4.mul_right hacopd
  have hone := factorsThrough_apply_eq_one_of_one_modEq hfactor hac hacop
  have hq := quadraticCharacter_apply_of_coprime d hdodd hacop
  simp only [ite_eq_right (by omega : ¬d % 4 = 1)] at hq
  have ha4int : (a : ℤ) % 4 = (1 : ℤ) % 4 := by exact_mod_cast ha4
  have hchi : ZMod.χ₄ ((a : ℤ) : ZMod 4) = 1 := by
    rw [ZMod.χ₄_int_one_mod_four]
    exact ha4int
  rw [haj, hchi] at hq
  have hval :=
    complexQuadraticCharacter_apply d hdodd ((a : ℤ) : ZMod (4 * d))
  have hone' :
    ((quadraticCharacter d hdodd) ((a : ℤ) : ZMod (4 * d)) : ℂ) = 1 := by
    rw [← hval]
    exact hone
  rw [hq] at hone'
  norm_num only at hone'

/-- The same proper-divisor obstruction holds for the complex-valued quadratic character. -/
theorem complexQuadraticCharacter_not_factorsThrough_proper_divisor_of_mod_four_eq_one {d c : ℕ}
    {hdodd : Odd d} (hdsq : Squarefree d) (hd4 : d % 4 = 1) (hc : c ∣ d) (hnot : ¬d ∣ c) :
    ¬DirichletCharacter.FactorsThrough (complexQuadraticCharacter d hdodd)
        c := by
  intro hfactor
  obtain ⟨a, haodd, hac, haj⟩ :=
    exists_nat_odd_one_modEq_and_jacobiSym_eq_neg_one hdodd hdsq hc hnot
  have hacopd : Nat.Coprime a d := by
    rw [Nat.coprime_iff_gcd_eq_one]
    by_contra hne
    have hz : jacobiSym (a : ℤ) d = 0 := by
      apply (jacobiSym.eq_zero_iff).mpr
      exact ⟨(Odd.pos hdodd).ne', by simpa only [Int.gcd_natCast_natCast, ne_eq] using hne⟩
    rw [hz] at haj
    norm_num only at haj
  have hacop4 : Nat.Coprime a 4 := by
    simpa only [pow_two] using Nat.Coprime.mul_right haodd.coprime_two_right haodd.coprime_two_right
  have hacop : Nat.Coprime a (4 * d) := hacop4.mul_right hacopd
  have hone := factorsThrough_apply_eq_one_of_one_modEq hfactor hac hacop
  have hval :=
    complexQuadraticCharacter_apply d hdodd ((a : ℤ) : ZMod (4 * d))
  have hq := quadraticCharacter_apply_of_coprime d hdodd hacop
  simp only [ite_eq_left hd4] at hq
  rw [haj] at hq
  have hone' :
    ((quadraticCharacter d hdodd) ((a : ℤ) : ZMod (4 * d)) : ℂ) = 1 := by
    rw [← hval]
    exact hone
  rw [hq] at hone'
  norm_num only at hone'

/-- The CRT obstruction remains valid for `n = b²*d`: the prime representative is
chosen coprime to the square factor, and hence is a unit at the original level. -/
theorem complexQuadraticCharacter_not_factorsThrough_proper_squarefreePart_of_mod_four_eq_one
    {n c : ℕ} {hn : Odd n} {hns : ¬IsSquare n} [NeZero (4 * n)]
    (bridge : JacobiCharacterArithmeticData n hn hns)
    (hd4 : bridge.squarefreePart % 4 = 1) (hc : c ∣ bridge.squarefreePart)
    (hnot : ¬bridge.squarefreePart ∣ c) :
    ¬DirichletCharacter.FactorsThrough (complexQuadraticCharacter n hn)
        c := by
  intro hfactor
  obtain ⟨a, haodd, hac, haj, hacopFactor⟩ :=
    exists_nat_odd_one_modEq_and_jacobiSym_eq_neg_one_coprime
      bridge.squarefreePart_odd bridge.squarefreePart_squarefree hc hnot
      (Odd.pos bridge.squareFactor_odd)
  have hacopd : Nat.Coprime a bridge.squarefreePart := by
    rw [Nat.coprime_iff_gcd_eq_one]
    by_contra hne
    have hz : jacobiSym (a : ℤ) bridge.squarefreePart = 0 := by
      apply (jacobiSym.eq_zero_iff).mpr
      exact
        ⟨bridge.squarefreePart_pos.ne', by simpa only [Int.gcd_natCast_natCast, ne_eq] using hne⟩
    rw [hz] at haj
    norm_num only at haj
  have hacopSquare : Nat.Coprime a (bridge.squareFactor ^ 2) := by
    simpa only [pow_two] using Nat.Coprime.mul_right hacopFactor hacopFactor
  have hnfactor : bridge.squareFactor ^ 2 * bridge.squarefreePart = n :=
    bridge.squarefreePart_sq_mul
  have hacopn : Nat.Coprime a n := by
    rw [← hnfactor]
    exact hacopSquare.mul_right hacopd
  have hacop : Nat.Coprime a (4 * n) :=
    (haodd.coprime_two_right.mul_right haodd.coprime_two_right).mul_right hacopn
  have hone := factorsThrough_apply_eq_one_of_one_modEq hfactor hac hacop
  have hq :=
    quadraticCharacter_apply_of_squarefreePart_coprime bridge hacop
  simp only [ite_eq_left hd4] at hq
  have hval :=
    complexQuadraticCharacter_apply n hn ((a : ℤ) : ZMod (4 * n))
  have hone' :
    ((quadraticCharacter n hn) ((a : ℤ) : ZMod (4 * n)) : ℂ) = 1 := by
    rw [← hval]
    exact hone
  rw [haj] at hq
  rw [hq] at hone'
  norm_num only at hone'

/-- In the `d = 3 mod 4` branch, a proper divisor missing an odd factor is excluded at the
bridge level by a representative that is also coprime to the square factor. -/
theorem complexQuadraticCharacter_not_factorsThrough_proper_squarefreePart_of_mod_four_eq_three
    {n c : ℕ} {hn : Odd n} {hns : ¬IsSquare n} [NeZero (4 * n)]
    (bridge : JacobiCharacterArithmeticData n hn hns)
    (hd4 : bridge.squarefreePart % 4 = 3) (hc : c ∣ 4 * bridge.squarefreePart)
    (hnot : ¬bridge.squarefreePart ∣ c) :
    ¬DirichletCharacter.FactorsThrough (complexQuadraticCharacter n hn)
        c := by
  intro hfactor
  obtain ⟨a, haodd, ha4, hac, haj, hacopFactor⟩ :=
    exists_nat_odd_one_modEq_and_jacobiSym_eq_neg_one_of_dvd_four_mul_coprime
      bridge.squarefreePart_odd bridge.squarefreePart_squarefree (Odd.pos bridge.squareFactor_odd)
      hc hnot
  have hacopd : Nat.Coprime a bridge.squarefreePart := by
    rw [Nat.coprime_iff_gcd_eq_one]
    by_contra hne
    have hz : jacobiSym (a : ℤ) bridge.squarefreePart = 0 := by
      apply (jacobiSym.eq_zero_iff).mpr
      exact
        ⟨bridge.squarefreePart_pos.ne', by simpa only [Int.gcd_natCast_natCast, ne_eq] using hne⟩
    rw [hz] at haj
    norm_num only at haj
  have hacopSquare : Nat.Coprime a (bridge.squareFactor ^ 2) := by
    simpa only [pow_two] using Nat.Coprime.mul_right hacopFactor hacopFactor
  have hacopn : Nat.Coprime a n := by
    rw [← bridge.squarefreePart_sq_mul]
    exact hacopSquare.mul_right hacopd
  have hacop : Nat.Coprime a (4 * n) :=
    (haodd.coprime_two_right.mul_right haodd.coprime_two_right).mul_right hacopn
  have hone := factorsThrough_apply_eq_one_of_one_modEq hfactor hac hacop
  have hq :=
    quadraticCharacter_apply_of_squarefreePart_coprime bridge hacop
  simp only [ite_eq_right (by omega : ¬bridge.squarefreePart % 4 = 1)] at hq
  have ha4int : (a : ℤ) % 4 = (1 : ℤ) % 4 := by exact_mod_cast ha4
  have hchi : ZMod.χ₄ ((a : ℤ) : ZMod 4) = 1 := by
    rw [ZMod.χ₄_int_one_mod_four]
    exact ha4int
  have hval :=
    complexQuadraticCharacter_apply n hn ((a : ℤ) : ZMod (4 * n))
  have hone' :
    ((quadraticCharacter n hn) ((a : ℤ) : ZMod (4 * n)) : ℂ) = 1 := by
    rw [← hval]
    exact hone
  rw [haj, hchi] at hq
  rw [hq] at hone'
  norm_num only at hone'

/-- The complex quadratic character has conductor dividing `d` in the `d = 1 mod 4` branch. -/
theorem complexQuadraticCharacter_conductor_dvd_squarefreePart_of_mod_four_eq_one {n : ℕ}
    {hn : Odd n} {hns : ¬IsSquare n} [NeZero (4 * n)]
    (bridge : JacobiCharacterArithmeticData n hn hns)
    (hdvd : bridge.squarefreePart ∣ n) (hd4 : bridge.squarefreePart % 4 = 1) :
    (complexQuadraticCharacter n hn).conductor ∣
      bridge.squarefreePart := by
  apply DirichletCharacter.conductor_dvd_of_mem_conductorSet
  exact
    (DirichletCharacter.mem_conductorSet_iff _).mpr
      (factorsThrough_ringHomComp_of_int
        (quadraticCharacter_factorsThrough_squarefreePart_of_mod_four_eq_one
          bridge hdvd hd4))

/-- In the `d = 1 mod 4` branch, the complex character has exactly the squarefree-part
conductor, not merely a divisor of it. -/
theorem complexQuadraticCharacter_conductor_eq_squarefreePart_of_mod_four_eq_one {n : ℕ}
    {hn : Odd n} {hns : ¬IsSquare n} [NeZero (4 * n)]
    (bridge : JacobiCharacterArithmeticData n hn hns)
    (hdvd : bridge.squarefreePart ∣ n) (hd4 : bridge.squarefreePart % 4 = 1) :
    (complexQuadraticCharacter n hn).conductor =
      bridge.squarefreePart := by
  apply Nat.dvd_antisymm
  · exact
      complexQuadraticCharacter_conductor_dvd_squarefreePart_of_mod_four_eq_one
        bridge hdvd hd4
  · by_contra hnot
    apply
      complexQuadraticCharacter_not_factorsThrough_proper_squarefreePart_of_mod_four_eq_one
        bridge hd4
        (complexQuadraticCharacter_conductor_dvd_squarefreePart_of_mod_four_eq_one
          bridge hdvd hd4)
        hnot
    exact
      DirichletCharacter.factorsThrough_conductor
        (complexQuadraticCharacter n hn)

/-- The complex quadratic character has conductor dividing `4*d` in the general branch. -/
theorem complexQuadraticCharacter_conductor_dvd_four_mul_squarefreePart {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} [NeZero (4 * n)]
    (bridge : JacobiCharacterArithmeticData n hn hns)
    (hdvd : bridge.squarefreePart ∣ n) :
    (complexQuadraticCharacter n hn).conductor ∣
      4 * bridge.squarefreePart := by
  apply DirichletCharacter.conductor_dvd_of_mem_conductorSet
  exact
    (DirichletCharacter.mem_conductorSet_iff _).mpr
      (factorsThrough_ringHomComp_of_int
        (quadraticCharacter_factorsThrough_squarefreePart bridge
          (Nat.mul_dvd_mul_left 4 hdvd)))

/-- In the `d = 3 mod 4` branch, the complex quadratic character has conductor `4*d`. -/
theorem complexQuadraticCharacter_conductor_eq_four_mul_squarefreePart_of_mod_four_eq_three {n : ℕ}
    {hn : Odd n} {hns : ¬IsSquare n} [NeZero (4 * n)]
    (bridge : JacobiCharacterArithmeticData n hn hns)
    (hdvd : bridge.squarefreePart ∣ n) (hd4 : bridge.squarefreePart % 4 = 3) :
    (complexQuadraticCharacter n hn).conductor =
      4 * bridge.squarefreePart := by
  apply Nat.dvd_antisymm
  · exact
      complexQuadraticCharacter_conductor_dvd_four_mul_squarefreePart
        bridge hdvd
  · by_contra hproper
    by_cases hdc :
      bridge.squarefreePart ∣ (complexQuadraticCharacter n hn).conductor
    · rcases
        eq_squarefreePart_or_two_mul_of_dvd_four_mul_of_dvd
          bridge.squarefreePart_odd
          (complexQuadraticCharacter_conductor_dvd_four_mul_squarefreePart
            bridge hdvd)
          hdc hproper with
        hcd | hcd
      · exact
          complexQuadraticCharacter_not_factorsThrough_eq_d_or_two_mul_of_bridge
            bridge hd4 (Or.inl hcd) (DirichletCharacter.factorsThrough_conductor _)
      · exact
          complexQuadraticCharacter_not_factorsThrough_eq_d_or_two_mul_of_bridge
            bridge hd4 (Or.inr hcd) (DirichletCharacter.factorsThrough_conductor _)
    · exact
        complexQuadraticCharacter_not_factorsThrough_proper_squarefreePart_of_mod_four_eq_three
          bridge hd4
          (complexQuadraticCharacter_conductor_dvd_four_mul_squarefreePart
            bridge hdvd)
          hdc (DirichletCharacter.factorsThrough_conductor _)

/-- Primitive normalization preserves the `4*d` conductor in the `d = 3 mod 4` branch. -/
theorem primitiveQuadraticCharacter_conductor_eq_discriminant_of_mod_four_eq_three {n : ℕ}
    {hn : Odd n} {hns : ¬IsSquare n} [NeZero (4 * n)]
    (bridge : JacobiCharacterArithmeticData n hn hns)
    (hdvd : bridge.squarefreePart ∣ n) (hd4 : bridge.squarefreePart % 4 = 3) :
    (primitiveQuadraticCharacter n hn).conductor =
      bridge.discriminant := by
  have hprim :
    (primitiveQuadraticCharacter n hn).conductor =
      (complexQuadraticCharacter n hn).conductor :=
    (DirichletCharacter.isPrimitive_def
          (primitiveQuadraticCharacter n hn)).mp
      (primitiveQuadraticCharacter_isPrimitive n hn)
  rw [hprim,
    complexQuadraticCharacter_conductor_eq_four_mul_squarefreePart_of_mod_four_eq_three
      bridge hdvd hd4,
    bridge.discriminant_eq, positiveFundamentalDiscriminant_eq_four_mul]
  exact by omega

/-- The primitive conductor divides the bridge discriminant in both fundamental-discriminant
branches. -/
theorem primitiveQuadraticCharacter_conductor_dvd_discriminant {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} [NeZero (4 * n)]
    (bridge : JacobiCharacterArithmeticData n hn hns) :
    (primitiveQuadraticCharacter n hn).conductor ∣
      bridge.discriminant := by
  have hdvd : bridge.squarefreePart ∣ n := by
    refine ⟨bridge.squareFactor ^ 2, ?_⟩
    simpa only [mul_comm] using bridge.squarefreePart_sq_mul.symm
  have hconductor :
    (primitiveQuadraticCharacter n hn).conductor =
      (complexQuadraticCharacter n hn).conductor :=
    (DirichletCharacter.isPrimitive_def
          (primitiveQuadraticCharacter n hn)).mp
      (primitiveQuadraticCharacter_isPrimitive n hn)
  rw [hconductor]
  rw [bridge.discriminant_eq]
  by_cases hd4 : bridge.squarefreePart % 4 = 1
  · rw [positiveFundamentalDiscriminant_eq_self hd4]
    exact complexQuadraticCharacter_conductor_dvd_squarefreePart_of_mod_four_eq_one bridge hdvd hd4
  · rw [positiveFundamentalDiscriminant_eq_four_mul hd4]
    exact complexQuadraticCharacter_conductor_dvd_four_mul_squarefreePart bridge hdvd

/-- In the `d = 1 mod 4` branch, primitive normalization preserves the exact discriminant
conductor obtained from the squarefree arithmetic bridge. -/
theorem primitiveQuadraticCharacter_conductor_eq_discriminant_of_mod_four_eq_one {n : ℕ}
    {hn : Odd n} {hns : ¬IsSquare n} [NeZero (4 * n)]
    (bridge : JacobiCharacterArithmeticData n hn hns)
    (hdvd : bridge.squarefreePart ∣ n) (hd4 : bridge.squarefreePart % 4 = 1) :
    (primitiveQuadraticCharacter n hn).conductor =
      bridge.discriminant := by
  have hprim :
    (primitiveQuadraticCharacter n hn).conductor =
      (complexQuadraticCharacter n hn).conductor :=
    (DirichletCharacter.isPrimitive_def
          (primitiveQuadraticCharacter n hn)).mp
      (primitiveQuadraticCharacter_isPrimitive n hn)
  rw [hprim,
    complexQuadraticCharacter_conductor_eq_squarefreePart_of_mod_four_eq_one
      bridge hdvd hd4]
  rw [bridge.discriminant_eq, positiveFundamentalDiscriminant_eq_self hd4]

/-- The primitive conductor equals the constructed discriminant in either odd squarefree branch. -/
theorem primitiveQuadraticCharacter_conductor_eq_discriminant {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} [NeZero (4 * n)]
    (bridge : JacobiCharacterArithmeticData n hn hns)
    (hdvd : bridge.squarefreePart ∣ n) :
    (primitiveQuadraticCharacter n hn).conductor =
      bridge.discriminant := by
  by_cases hd4 : bridge.squarefreePart % 4 = 1
  · exact
      primitiveQuadraticCharacter_conductor_eq_discriminant_of_mod_four_eq_one
        bridge hdvd hd4
  · have hd4' : bridge.squarefreePart % 4 = 3 := by
      rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp bridge.squarefreePart_odd) with h | h
      · exact False.elim (hd4 h)
      · exact h
    exact
      primitiveQuadraticCharacter_conductor_eq_discriminant_of_mod_four_eq_three
        bridge hdvd hd4'

theorem complexQuadraticCharacter_conductor_eq_discriminant {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : JacobiCharacterArithmeticData n hn hns)
    (hdvd : bridge.squarefreePart ∣ n) :
    (complexQuadraticCharacter n hn).conductor = bridge.discriminant := by
  let _ : NeZero (4 * n) :=
    ⟨by
      have hnpos : 0 < n := hn.pos
      omega⟩
  have hprim :
    (primitiveQuadraticCharacter n hn).conductor =
      (complexQuadraticCharacter n hn).conductor :=
    (DirichletCharacter.isPrimitive_def
          (primitiveQuadraticCharacter n hn)).mp
      (primitiveQuadraticCharacter_isPrimitive n hn)
  exact
    hprim.symm.trans
      (primitiveQuadraticCharacter_conductor_eq_discriminant bridge hdvd)

theorem primitiveQuadraticCharacter_conductor_odd_of_two_eq_one (n : ℕ) (hn : Odd n)
    (hc :
      primitiveQuadraticCharacter n hn
          (2 : ZMod (complexQuadraticCharacter n hn).conductor) =
        1) :
    Odd (complexQuadraticCharacter n hn).conductor := by
  by_contra hodd
  have heven : Even (complexQuadraticCharacter n hn).conductor :=
    Nat.not_odd_iff_even.mp hodd
  obtain ⟨k, hk⟩ := heven
  have hcop :
    ¬Nat.Coprime 2 (complexQuadraticCharacter n hn).conductor := by
    intro hcop
    have hodd' : Odd (complexQuadraticCharacter n hn).conductor :=
      Nat.Coprime.odd_of_left hcop
    obtain ⟨j, hj⟩ := hodd'
    omega
  have hunit :
    ¬IsUnit (2 : ZMod (complexQuadraticCharacter n hn).conductor) := by
    intro hunit
    exact
      hcop
        ((ZMod.isUnit_iff_coprime 2
              (complexQuadraticCharacter n hn).conductor).mp
          hunit)
  have hz := MulChar.map_nonunit (primitiveQuadraticCharacter n hn) hunit
  rw [hc] at hz
  norm_num only at hz

theorem JacobiCharacterArithmeticData.discriminant_eq_squarefreePart_of_two_eq_neg_one {n : ℕ}
    {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : JacobiCharacterArithmeticData n hn hns)
    (hcond :
      (complexQuadraticCharacter n hn).conductor = bridge.discriminant)
    (hc :
      primitiveQuadraticCharacter n hn
          (2 : ZMod (complexQuadraticCharacter n hn).conductor) =
        -1) :
    bridge.discriminant = bridge.squarefreePart := by
  let _ : NeZero (4 * n) :=
    ⟨by
      have hnpos : 0 < n := hn.pos
      omega⟩
  have hoddC : Odd (complexQuadraticCharacter n hn).conductor := by
    by_contra hodd
    have heven : Even (complexQuadraticCharacter n hn).conductor :=
      Nat.not_odd_iff_even.mp hodd
    obtain ⟨k, hk⟩ := heven
    have hcop :
      ¬Nat.Coprime 2 (complexQuadraticCharacter n hn).conductor := by
      intro hcop
      have hodd' : Odd (complexQuadraticCharacter n hn).conductor :=
        Nat.Coprime.odd_of_left hcop
      obtain ⟨j, hj⟩ := hodd'
      omega
    have hunit :
      ¬IsUnit (2 : ZMod (complexQuadraticCharacter n hn).conductor) := by
      intro hunit
      exact
        hcop
          ((ZMod.isUnit_iff_coprime 2
                (complexQuadraticCharacter n hn).conductor).mp
            hunit)
    have hz := MulChar.map_nonunit (primitiveQuadraticCharacter n hn) hunit
    rw [hc] at hz
    norm_num only at hz
  have hoddD : Odd bridge.discriminant := by
    rw [← hcond]
    exact hoddC
  have hdmod : bridge.squarefreePart % 4 = 1 := by
    by_contra hdmod
    rw [bridge.discriminant_eq,
      positiveFundamentalDiscriminant_eq_four_mul hdmod] at hoddD
    obtain ⟨k, hk⟩ := hoddD
    omega
  rw [bridge.discriminant_eq,
    positiveFundamentalDiscriminant_eq_self hdmod]

theorem JacobiCharacterArithmeticData.discriminant_eq_squarefreePart_of_two_eq_one {n : ℕ}
    {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : JacobiCharacterArithmeticData n hn hns)
    (hcond :
      (complexQuadraticCharacter n hn).conductor = bridge.discriminant)
    (hc :
      primitiveQuadraticCharacter n hn
          (2 : ZMod (complexQuadraticCharacter n hn).conductor) =
        1) :
    bridge.discriminant = bridge.squarefreePart := by
  let _ : NeZero (4 * n) :=
    ⟨by
      have hnpos : 0 < n := hn.pos
      omega⟩
  have hoddD : Odd bridge.discriminant := by
    rw [← hcond]
    exact primitiveQuadraticCharacter_conductor_odd_of_two_eq_one n hn hc
  have hdmod : bridge.squarefreePart % 4 = 1 := by
    by_contra hdmod
    rw [bridge.discriminant_eq,
      positiveFundamentalDiscriminant_eq_four_mul hdmod] at hoddD
    obtain ⟨k, hk⟩ := hoddD
    omega
  rw [bridge.discriminant_eq,
    positiveFundamentalDiscriminant_eq_self hdmod]

/--
Input/assumptions: the arithmetic bridge and the odd fundamental-discriminant branch.
Conclusion: the primitive conductor is exactly the squarefree part `d`.
Content: combine the conductor/discriminant equality with the fundamental-discriminant definition.
Role: identifies the primitive conductor with `d` whenever `d % 4 = 1`.
-/
theorem primitiveQuadraticCharacter_conductor_eq_squarefreePart_of_mod_four_eq_one {n : ℕ}
    {hn : Odd n} {hns : ¬IsSquare n} [NeZero (4 * n)]
    (bridge : JacobiCharacterArithmeticData n hn hns)
    (hdvd : bridge.squarefreePart ∣ n) (hd4 : bridge.squarefreePart % 4 = 1) :
    (primitiveQuadraticCharacter n hn).conductor =
      bridge.squarefreePart := by
  rw [primitiveQuadraticCharacter_conductor_eq_discriminant bridge hdvd,
    bridge.discriminant_eq, positiveFundamentalDiscriminant_eq_self hd4]

/--
Input/assumptions: the squarefree part is `1 mod 4`, as in `PseudoPrime.NumberTheory.`
`primitiveQuadraticCharacter_conductor_eq_squarefreePart_of_mod_four_eq_one`.
Conclusion: the logarithm of the primitive conductor equals `log d`.
Content: rewrite the conductor using the exact arithmetic identity.
Role: expresses the log conductor exactly as `log d`, rather than bounding it by `log(4*d)`.
-/
theorem primitiveQuadraticCharacter_log_conductor_eq_log_squarefreePart_of_mod_four_eq_one {n : ℕ}
    {hn : Odd n} {hns : ¬IsSquare n} [NeZero (4 * n)]
    (bridge : JacobiCharacterArithmeticData n hn hns)
    (hdvd : bridge.squarefreePart ∣ n) (hd4 : bridge.squarefreePart % 4 = 1) :
    Real.log (primitiveQuadraticCharacter n hn).conductor =
      Real.log bridge.squarefreePart := by
  rw [primitiveQuadraticCharacter_conductor_eq_squarefreePart_of_mod_four_eq_one bridge hdvd hd4]

/-- A prime divisor of `n` is an immediate `≠ 1` Jacobi witness. -/
theorem primeNeOneWitness_mem_of_dvd {n p : ℕ} (hp : p.Prime) (hodd : Odd p) (hpdvd : p ∣ n) :
    p ∈ PrimeNeOneWitnessSet n := by
  refine ⟨hp, hodd, ?_⟩
  have hnotcop : ¬Nat.Coprime n p := by
    intro hcop
    have hcop' : Nat.Coprime p n := hcop.symm
    exact (hp.dvd_iff_not_coprime.mp hpdvd) hcop'
  have hgcd : (n : ℤ).gcd (p : ℤ) ≠ 1 := by
    intro hgcd
    have hcopz : IsCoprime (n : ℤ) (p : ℤ) := Int.isCoprime_iff_gcd_eq_one.mpr hgcd
    have hcop : Nat.Coprime n p := Int.isCoprime_iff_nat_coprime.mp hcopz
    exact hnotcop hcop
  have hz : jacobiSym (n : ℤ) p = 0 := jacobiSym.eq_zero_iff.mpr ⟨hp.ne_zero, hgcd⟩
  intro hone
  omega

/-- A nontrivial complex quadratic-character value at an odd prime gives a `≠ 1` witness. -/
theorem primeNeOneWitness_mem_of_complexQuadraticCharacter_ne_one {n p : ℕ} (hn : Odd n)
    (hp : p.Prime) (_hodd : Odd p) (hpdvd : ¬p ∣ 4 * n)
    (hchar : complexQuadraticCharacter n hn p ≠ 1) :
    p ∈ PrimeNeOneWitnessSet n := by
  exact
    PrimeNegOneWitnessSet.subset_primeNeOneWitnessSet n
      (primeNegOneWitness_mem_of_complexQuadraticCharacter_ne_one n hn hp
        hpdvd hchar)

/--
Input/assumptions: an odd nonsquare `n`, its squarefree bridge, and an odd-prime `≠ 1` witness
for the squarefree part.
Conclusion: the same prime is an odd-prime `≠ 1` witness for `n`.
Content: if the prime divides `n`, its Jacobi value is zero; otherwise the square factor is
invisible to the Jacobi symbol.
Proof: split on divisibility and use the squarefree-part coprimality lemma in the nondividing case.
Role: transfers any squarefree-part witness to the original nonsquare input.
-/
theorem primeNeOneWitness_mem_of_squarefreePart_mem {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : JacobiCharacterArithmeticData n hn hns) {p : ℕ}
    (hp : p ∈ PrimeNeOneWitnessSet bridge.squarefreePart) :
    p ∈ PrimeNeOneWitnessSet n := by
  rcases hp with ⟨hpp, hodd, hvalue⟩
  by_cases hpdvd : p ∣ n
  · exact primeNeOneWitness_mem_of_dvd hpp hodd hpdvd
  · refine ⟨hpp, hodd, ?_⟩
    have hcop : Nat.Coprime n p := by exact (hpp.coprime_iff_not_dvd.mpr hpdvd).symm
    have heq := jacobiSym_eq_squarefreePart_of_coprime bridge hcop
    intro hone
    apply hvalue
    rw [← heq]
    exact hone

/--
Input/assumptions: a nonempty `≠ 1` witness set for the squarefree part of an odd nonsquare.
Conclusion: the least witness for `n` is no larger than the least witness for its squarefree part.
Content: transfer the squarefree least witness first, then apply the least-element property.
Role: transfers numerical upper bounds on the least squarefree-part witness.
-/
theorem primeNeOneWitness_le_of_squarefreePart {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : JacobiCharacterArithmeticData n hn hns)
    {hd : (PrimeNeOneWitnessSet bridge.squarefreePart).Nonempty} :
    primeNeOneWitness n
        (show (PrimeNeOneWitnessSet n).Nonempty from by
          obtain ⟨p, hp⟩ := hd
          exact
            ⟨p, primeNeOneWitness_mem_of_squarefreePart_mem bridge hp⟩) ≤
      primeNeOneWitness bridge.squarefreePart hd := by
  let hdn : (PrimeNeOneWitnessSet n).Nonempty := by
    obtain ⟨p, hp⟩ := hd
    exact ⟨p, primeNeOneWitness_mem_of_squarefreePart_mem bridge hp⟩
  have hp := primeNeOneWitness_mem bridge.squarefreePart hd
  have hpn := primeNeOneWitness_mem_of_squarefreePart_mem bridge hp
  exact primeNeOneWitness_le n hdn hpn

/-- A fixed squarefree-part witness can be transferred together with its numerical cutoff. -/
theorem exists_primeNeOneWitness_le_of_squarefreePart_eq {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : JacobiCharacterArithmeticData n hn hns) {d p : ℕ}
    (hd : bridge.squarefreePart = d) (hpp : p.Prime) (hodd : Odd p) (hvalue : jacobiSym d p ≠ 1) :
    ∃ hdn : (PrimeNeOneWitnessSet n).Nonempty,
      primeNeOneWitness n hdn ≤ p := by
  have hpd : p ∈ PrimeNeOneWitnessSet bridge.squarefreePart := by
    rw [hd]
    exact ⟨hpp, hodd, hvalue⟩
  have hpn := primeNeOneWitness_mem_of_squarefreePart_mem bridge hpd
  let hdn : (PrimeNeOneWitnessSet n).Nonempty := ⟨p, hpn⟩
  exact ⟨hdn, primeNeOneWitness_le n hdn hpn⟩

/-- The prime `3` witnesses `jacobiSym 5 3 ≠ 1`, by its Legendre-symbol power identity. -/
theorem jacobiSym_five_three_ne_one : jacobiSym 5 3 ≠ 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [← jacobiSym.legendreSym.to_jacobiSym 3 5]
  intro h
  have hpow := legendreSym.eq_pow 3 5
  rw [h] at hpow
  have hne : (1 : ZMod 3) ≠ 5 := by
    intro hmod
    have hval := congrArg ZMod.val hmod
    change 1 = 2 at hval
    norm_num only at hval
  exact hne hpow

/-- The prime `5` witnesses `jacobiSym 7 5 ≠ 1`, by its Legendre-symbol power identity. -/
theorem jacobiSym_seven_five_ne_one : jacobiSym 7 5 ≠ 1 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  rw [← jacobiSym.legendreSym.to_jacobiSym 5 7]
  intro h
  have hpow := legendreSym.eq_pow 5 7
  rw [h] at hpow
  have hne : (1 : ZMod 5) ≠ 7 ^ ((5 - 1) / 2) := by
    intro hmod
    have hval := congrArg ZMod.val hmod
    change 1 = 4 at hval
    norm_num only at hval
  exact hne hpow

private lemma three_le_log_sq_of_eleven_le {n : ℕ} (hn : 11 ≤ n) : (3 : ℝ) ≤ (Real.log n) ^ 2 := by
  have hnpos : 0 < (n : ℝ) := by positivity
  have hn8 : 8 ≤ n := by omega
  have h8n :=
    Real.strictMonoOn_log.monotoneOn (show 0 < (8 : ℝ) by norm_num only) hnpos
      (by exact_mod_cast hn8)
  have hlog8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num only, Real.log_pow]
    norm_num only
  have hlog : 2 < Real.log n := by linarith only [h8n, hlog8, Real.log_two_gt_d9]
  nlinarith only [hlog]

private lemma five_le_log_sq_of_twenty_eight_le {n : ℕ} (hn : 28 ≤ n) :
    (5 : ℝ) ≤ (Real.log n) ^ 2 := by
  have hnpos : 0 < (n : ℝ) := by positivity
  have hn16 : 16 ≤ n := by omega
  have h16n :=
    Real.strictMonoOn_log.monotoneOn (show 0 < (16 : ℝ) by norm_num only) hnpos
      (by exact_mod_cast hn16)
  have hlog16 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num only, Real.log_pow]
    norm_num only
  have hlog : 2.7 < Real.log n := by linarith only [h16n, hlog16, Real.log_two_gt_d9]
  nlinarith only [hlog]

/--
Input/assumptions: an odd nonsquare bridge whose squarefree part is one of `3`, `5`, or `7`,
and `11 ≤ n`.
Conclusion: the least transferred `≠ 1` witness is at most `(log n)^2`.
Content: use the fixed witnesses `3`, `3`, and `5` in the three small squarefree cases.
Proof: transfer the fixed witness and use elementary logarithmic lower bounds; the `7` case forces
the square factor to be at least `2`, hence `n ≥ 28`.
Role: supplies an unconditional logarithmic-square witness bound for these three squarefree parts.
-/
theorem exists_primeNeOneWitness_cast_le_log_sq_of_small_squarefreePart {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} (bridge : JacobiCharacterArithmeticData n hn hns)
    (hn11 : 11 ≤ n)
    (hd : bridge.squarefreePart = 3 ∨ bridge.squarefreePart = 5 ∨ bridge.squarefreePart = 7) :
    ∃ hdn : (PrimeNeOneWitnessSet n).Nonempty,
      (primeNeOneWitness n hdn : ℝ) ≤ (Real.log n) ^ 2 := by
  rcases hd with h3 | h5 | h7
  · have hzero : jacobiSym (3 : ℤ) 3 = 0 := by
      apply jacobiSym.eq_zero_iff.mpr
      exact ⟨Nat.prime_three.ne_zero, by norm_num only⟩
    have hmem : (3 : ℕ) ∈ PrimeNeOneWitnessSet 3 := by
      refine ⟨Nat.prime_three, by decide, ?_⟩
      change jacobiSym (3 : ℤ) 3 ≠ 1
      rw [hzero]
      norm_num only
    obtain ⟨hdn, hle⟩ :=
      exists_primeNeOneWitness_le_of_squarefreePart_eq bridge h3
        Nat.prime_three (by decide) (by simpa only [Nat.cast_ofNat, ne_eq] using hmem.2.2)
    refine ⟨hdn, ?_⟩
    have hbound := three_le_log_sq_of_eleven_le hn11
    have hle' : (primeNeOneWitness n hdn : ℝ) ≤ 3 := by exact_mod_cast hle
    exact hle'.trans hbound
  · obtain ⟨hdn, hle⟩ :=
      exists_primeNeOneWitness_le_of_squarefreePart_eq bridge h5
        Nat.prime_three (by decide) jacobiSym_five_three_ne_one
    refine ⟨hdn, ?_⟩
    have hbound := three_le_log_sq_of_eleven_le hn11
    have hle' : (primeNeOneWitness n hdn : ℝ) ≤ 3 := by exact_mod_cast hle
    exact hle'.trans hbound
  · obtain ⟨hdn, hle⟩ :=
      exists_primeNeOneWitness_le_of_squarefreePart_eq bridge h7
        Nat.prime_five (by decide) jacobiSym_seven_five_ne_one
    refine ⟨hdn, ?_⟩
    have hfactor : bridge.squareFactor ^ 2 * 7 = n := by
      simpa only [h7] using bridge.squarefreePart_sq_mul
    have hb : 2 ≤ bridge.squareFactor := by
      by_contra hsmall
      have hsmall' : bridge.squareFactor = 0 ∨ bridge.squareFactor = 1 := by omega
      rcases hsmall' with hzero | hone
      · rw [hzero] at hfactor
        norm_num only at hfactor
        omega
      · rw [hone] at hfactor
        omega
    have hn28 : 28 ≤ n := by
      have hsquare : 2 * 2 ≤ bridge.squareFactor * bridge.squareFactor :=
        Nat.mul_self_le_mul_self hb
      calc
        28 = 2 * 2 * 7 := by norm_num only
        _ ≤ (bridge.squareFactor * bridge.squareFactor) * 7 := Nat.mul_le_mul_right 7 hsquare
        _ = n := by simpa only [pow_two] using hfactor
    have hbound := five_le_log_sq_of_twenty_eight_le hn28
    have hle' : (primeNeOneWitness n hdn : ℝ) ≤ 5 := by exact_mod_cast hle
    exact hle'.trans hbound

/--
Input/assumptions: the squarefree part of an odd nonsquare bridge is not one of `3`, `5`, or `7`.
Conclusion: its odd squarefree part is at least `11`.
Content: oddness leaves only `9` below `11` after the excluded values, while squarefreeness
eliminates `9`.
Role: separates the three small squarefree parts from the range `d ≥ 11`.
-/
theorem JacobiCharacterArithmeticData.squarefreePart_ge_eleven_of_not_small {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} (bridge : JacobiCharacterArithmeticData n hn hns)
    (h3 : bridge.squarefreePart ≠ 3) (h5 : bridge.squarefreePart ≠ 5)
    (h7 : bridge.squarefreePart ≠ 7) : 11 ≤ bridge.squarefreePart := by
  have h9 : bridge.squarefreePart ≠ 9 := by
    intro h
    have hsq :=
      (Nat.squarefree_iff_prime_squarefree.mp bridge.squarefreePart_squarefree) 3 Nat.prime_three
    apply hsq
    rw [h]
  by_contra hlt
  have hle : bridge.squarefreePart ≤ 10 := by omega
  have hodd := bridge.squarefreePart_odd
  have hgt := bridge.squarefreePart_gt_one
  interval_cases bridge.squarefreePart
  all_goals
    first
    | omega
    | exact h3 rfl
    | exact h5 rfl
    | exact h7 rfl
    | exact h9 rfl
    | obtain ⟨k, hk⟩ := hodd; omega

/-- For an odd nonsquare arithmetic bridge with squarefree part `d`, define the real parameter
`y = log d`. The cutoff and conductor inequalities below use this same parameter. -/
noncomputable def JacobiCharacterArithmeticData.y {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : JacobiCharacterArithmeticData n hn hns) : ℝ :=
  Real.log (bridge.squarefreePart : ℝ)

/--
Input/assumptions: a bridge, a positive integer cutoff `N`, and `N ≤ d` together with
`48 ≤ log N`.
Conclusion: the bridge radius `y = log d` lies in the analytic range `y ≥ 48`.
Content: monotonicity of the real logarithm transfers the certified integer cutoff to the
squarefree part without unfolding the fundamental-discriminant branches.
Role: transfers an integer cutoff certificate to the real parameter `y = log d`.
-/
theorem JacobiCharacterArithmeticData.y_ge_of_nat_cutoff {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : JacobiCharacterArithmeticData n hn hns) {N : ℕ}
    (hNpos : 0 < N) (hN : 48 ≤ Real.log (N : ℝ)) (hNd : N ≤ bridge.squarefreePart) :
    48 ≤ bridge.y := by
  have hNposR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hdposR : (0 : ℝ) < bridge.squarefreePart := by exact_mod_cast bridge.squarefreePart_pos
  have hleR : (N : ℝ) ≤ bridge.squarefreePart := by exact_mod_cast hNd
  have hlog := Real.strictMonoOn_log.monotoneOn hNposR hdposR hleR
  dsimp [JacobiCharacterArithmeticData.y]
  exact hN.trans hlog

/--
Input/assumptions: a bridge, a positive integer cutoff `N`, and `N ≤ d` together with
`12 ≤ log N`.
Conclusion: the bridge parameter `y = log d` satisfies `y ≥ 12`.
Proof and role: monotonicity of the logarithm transfers the integer cutoff certificate.
-/
theorem JacobiCharacterArithmeticData.y_ge_of_nat_cutoff_of_twelve {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} (bridge : JacobiCharacterArithmeticData n hn hns)
    {N : ℕ} (hNpos : 0 < N) (hN : 12 ≤ Real.log (N : ℝ)) (hNd : N ≤ bridge.squarefreePart) :
    12 ≤ bridge.y := by
  have hNposR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hdposR : (0 : ℝ) < bridge.squarefreePart := by exact_mod_cast bridge.squarefreePart_pos
  have hleR : (N : ℝ) ≤ bridge.squarefreePart := by exact_mod_cast hNd
  have hlog := Real.strictMonoOn_log.monotoneOn hNposR hdposR hleR
  dsimp [JacobiCharacterArithmeticData.y]
  exact hN.trans hlog

/-- The positive fundamental discriminant of the squarefree part `d` is at most `4*d`. -/
theorem JacobiCharacterArithmeticData.discriminant_le_four_mul_squarefreePart {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} (bridge : JacobiCharacterArithmeticData n hn hns) :
    bridge.discriminant ≤ 4 * bridge.squarefreePart := by
  rw [bridge.discriminant_eq]
  by_cases hd4 : bridge.squarefreePart % 4 = 1
  · rw [positiveFundamentalDiscriminant_eq_self hd4]
    exact Nat.le_mul_of_pos_left bridge.squarefreePart (by norm_num only)
  · rw [positiveFundamentalDiscriminant_eq_four_mul hd4]

/-- Positivity and `discriminant ≤ 4*d` give `log discriminant ≤ log d + log 4`. -/
theorem JacobiCharacterArithmeticData.log_discriminant_le_y_add_log_four {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} (bridge : JacobiCharacterArithmeticData n hn hns) :
    Real.log (bridge.discriminant : ℝ) ≤ bridge.y + Real.log 4 := by
  have hdpos : 0 < (bridge.squarefreePart : ℝ) := by exact_mod_cast bridge.squarefreePart_pos
  have hDpos : 0 < (bridge.discriminant : ℝ) := by exact_mod_cast bridge.discriminant_pos
  have hprodpos : 0 < (4 * (bridge.squarefreePart : ℝ)) := by positivity
  have hle : (bridge.discriminant : ℝ) ≤ 4 * (bridge.squarefreePart : ℝ) := by
    exact_mod_cast bridge.discriminant_le_four_mul_squarefreePart
  have hlog := Real.strictMonoOn_log.monotoneOn hDpos hprodpos hle
  rw [Real.log_mul (by norm_num only) (by positivity)] at hlog
  simpa only [y, ge_iff_le, add_comm] using hlog

/--
Input/assumptions: an arithmetic bridge with its canonical nonzero conductor.
Conclusion: the bridge character conductor is the constructed fundamental discriminant.
Content: transfer the existing primitive-conductor identity across `character_eq`.
Role: supplies the exact modulus in conductor and logarithmic comparisons.
-/
theorem JacobiCharacterArithmeticData.character_conductor_eq_discriminant {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} [NeZero (complexQuadraticCharacter n hn).conductor]
    (bridge : JacobiCharacterArithmeticData n hn hns) :
    bridge.character.conductor = bridge.discriminant := by
  let _ : NeZero (4 * n) :=
    ⟨by
      have hnpos : 0 < n := hn.pos
      omega⟩
  have hdvd : bridge.squarefreePart ∣ n := by
    exact
      ⟨bridge.squareFactor ^ 2, by
        simpa only [Nat.mul_comm] using bridge.squarefreePart_sq_mul.symm⟩
  have hprim :=
    primitiveQuadraticCharacter_conductor_eq_discriminant bridge hdvd
  have hchar :
    bridge.character.conductor =
      (primitiveQuadraticCharacter n hn).conductor := by
    rw [bridge.character_eq]
  exact hchar.trans hprim

theorem JacobiCharacterArithmeticData.log_character_conductor_le_of_discriminant_le {n : ℕ}
    {hn : Odd n} {hns : ¬IsSquare n}
    [NeZero (complexQuadraticCharacter n hn).conductor]
    (bridge : JacobiCharacterArithmeticData n hn hns)
    (hD : bridge.discriminant ≤ bridge.squarefreePart) :
    Real.log bridge.character.conductor ≤ bridge.y := by
  have hcond := bridge.character_conductor_eq_discriminant
  have hDpos : (0 : ℝ) < bridge.discriminant := by exact_mod_cast bridge.discriminant_pos
  have hdpos : (0 : ℝ) < bridge.squarefreePart := by exact_mod_cast bridge.squarefreePart_pos
  have hle : (bridge.discriminant : ℝ) ≤ bridge.squarefreePart := by exact_mod_cast hD
  have hlog := Real.strictMonoOn_log.monotoneOn hDpos hdpos hle
  rw [hcond]
  simpa only [y, ge_iff_le] using hlog

/--
Input/assumptions: an odd nonsquare arithmetic bridge and the divisibility of its squarefree part.
Conclusion: the primitive quadratic conductor satisfies
`log conductor ≤ y + log 4`.
Content: first identify the primitive conductor with the fundamental discriminant, then reuse the
bridge discriminant estimate without changing the analytic radius.
Role: bounds the log conductor in terms of the squarefree-part parameter, without a condition on
the character value at `2`.
-/
theorem JacobiCharacterArithmeticData.log_primitiveQuadraticCharacter_conductor_le_y_add_log_four
    {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n} [NeZero (4 * n)]
    (bridge : JacobiCharacterArithmeticData n hn hns)
    (hdvd : bridge.squarefreePart ∣ n) :
    Real.log (primitiveQuadraticCharacter n hn).conductor ≤
      bridge.y + Real.log 4 := by
  rw [primitiveQuadraticCharacter_conductor_eq_discriminant bridge hdvd]
  exact bridge.log_discriminant_le_y_add_log_four

theorem JacobiCharacterArithmeticData.log_character_conductor_le_y_add_log_four {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} [NeZero (complexQuadraticCharacter n hn).conductor]
    (bridge : JacobiCharacterArithmeticData n hn hns) :
    Real.log bridge.character.conductor ≤ bridge.y + Real.log 4 := by
  let _ : NeZero (4 * n) :=
    ⟨by
      have hnpos : 0 < n := hn.pos
      omega⟩
  have hdvd : bridge.squarefreePart ∣ n := by
    exact
      ⟨bridge.squareFactor ^ 2, by
        simpa only [Nat.mul_comm] using bridge.squarefreePart_sq_mul.symm⟩
  rw [bridge.character_eq]
  exact bridge.log_primitiveQuadraticCharacter_conductor_le_y_add_log_four hdvd

/-- Every value of the complex quadratic character is `0`, `1`, or `-1`. -/
theorem complexQuadraticCharacter_eq_zero_or_eq_one_or_eq_neg_one (n : ℕ) (hn : Odd n)
    (a : ZMod (4 * n)) :
    complexQuadraticCharacter n hn a = 0 ∨
      complexQuadraticCharacter n hn a = 1 ∨
      complexQuadraticCharacter n hn a = -1 := by
  classical
  by_cases ha : IsUnit a
  · rcases ha with ⟨u, rfl⟩
    right
    have hsq :
      (complexQuadraticCharacter n hn (↑u : ZMod (4 * n))) ^ 2 = 1 := by
      rw [← MulChar.pow_apply_coe, complexQuadraticCharacter_sq]
      exact MulChar.one_apply_coe u
    exact sq_eq_one_iff.mp hsq
  · left
    exact MulChar.map_nonunit (complexQuadraticCharacter n hn) ha

/-- Under a no-small-witness hypothesis, an odd prime divisor cannot occur below the cutoff. -/
theorem not_dvd_of_no_primeNeOne_witness {n X p : ℕ} (hp : p.Prime) (hodd : Odd p) (hpX : p ≤ X)
    (hno : ∀ q, q.Prime → Odd q → q ≤ X → q ∉ PrimeNeOneWitnessSet n) :
    ¬p ∣ n := by
  intro hpdvd
  exact hno p hp hodd hpX (primeNeOneWitness_mem_of_dvd hp hodd hpdvd)

/-- Away from divisors, the no-small-witness hypothesis forces the complex character value to one.
-/
theorem complexQuadraticCharacter_eq_one_of_no_primeNeOne_witness {n X p : ℕ} (hn : Odd n)
    (hp : p.Prime) (hodd : Odd p) (hpX : p ≤ X)
    (hno : ∀ q, q.Prime → Odd q → q ≤ X → q ∉ PrimeNeOneWitnessSet n)
    (hpdvd : ¬p ∣ n) : complexQuadraticCharacter n hn p = 1 := by
  have hpdvd4 : ¬p ∣ 4 * n := by
    intro h
    rcases hp.dvd_mul.mp h with h4 | hn'
    · have hpdiv2 : p ∣ 2 := hp.dvd_of_dvd_pow (by simpa only [Nat.reducePow] using h4 : p ∣ 2 ^ 2)
      have hp2 : p = 2 := by
        rcases (Nat.dvd_prime Nat.prime_two).mp hpdiv2 with hp1 | hp2
        · exact False.elim (hp.ne_one hp1)
        · exact hp2
      rw [hp2] at hodd
      obtain ⟨k, hk⟩ := hodd
      omega
    · exact hpdvd hn'
  have hmem : p ∉ PrimeNeOneWitnessSet n := hno p hp hodd hpX
  have hchar_ne : ¬complexQuadraticCharacter n hn p ≠ 1 := by
    intro hchar
    exact
      hmem
        (primeNeOneWitness_mem_of_complexQuadraticCharacter_ne_one hn hp
          hodd hpdvd4 hchar)
  exact not_not.mp hchar_ne

/-- At an odd prime away from `n`, the primitive character has the Jacobi value. -/
theorem primitiveQuadraticCharacter_apply_odd_prime {n p : ℕ} (hn : Odd n) (hp : p.Prime)
    (hodd : Odd p) (hpdvd : ¬p ∣ n) :
    primitiveQuadraticCharacter n hn (p : ℤ) = (jacobiSym n p : ℂ) := by
  have hp4 : Nat.Coprime p 4 := by
    apply hp.coprime_iff_not_dvd.mpr
    intro hp4
    have hpdiv2 : p ∣ 2 := hp.dvd_of_dvd_pow (by simpa only [Nat.reducePow] using hp4 : p ∣ 2 ^ 2)
    have hp2 : p = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hpdiv2 with hp1 | hp2
      · exact False.elim (hp.ne_one hp1)
      · exact hp2
    rw [hp2] at hodd
    obtain ⟨k, hk⟩ := hodd
    omega
  have hcop : IsCoprime (p : ℤ) (4 * (n : ℤ)) :=
    (hp4.mul_right (hp.coprime_iff_not_dvd.mpr hpdvd)).isCoprime
  rw [primitiveQuadraticCharacter_apply_of_isCoprime n hn hcop]
  simpa only [Int.cast_natCast] using
    complexQuadraticCharacter_apply_odd_prime n hn hp hodd
      (hp.coprime_iff_not_dvd.mpr hpdvd)

/-- The primitive character is one at every odd prime below `X` when no witness exists. -/
theorem primitiveQuadraticCharacter_eq_one_of_no_primeNeOne_witness {n X p : ℕ} (hn : Odd n)
    (hp : p.Prime) (hodd : Odd p) (hpX : p ≤ X)
    (hno : ∀ q, q.Prime → Odd q → q ≤ X → q ∉ PrimeNeOneWitnessSet n)
    (hpdvd : ¬p ∣ n) : primitiveQuadraticCharacter n hn (p : ℤ) = 1 := by
  rw [primitiveQuadraticCharacter_apply_odd_prime hn hp hodd hpdvd]
  have hj : jacobiSym n p = 1 := by
    by_contra hne
    exact (hno p hp hodd hpX) ⟨hp, hodd, hne⟩
  simp only [hj, Int.cast_one]

/--
Input/assumptions: an arithmetic bridge and a no-small-witness hypothesis up to `X`.
Conclusion: the bridge character is one at every odd prime at most `X`.
Content: this is the adapter from the arithmetic bridge's canonical primitive character to the
analytic `DirichletCharacter` used by the three branch downstream theorems.
Proof: first obtain non-divisibility from the no-witness hypothesis, then rewrite the bridge
character using `character_eq` and apply the primitive-character lemma above.
Role: supplies exact character values under a no-witness cutoff hypothesis.
-/
theorem JacobiCharacterArithmeticData.character_eq_one_of_no_primeNeOne_witness {n X p : ℕ}
    {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : JacobiCharacterArithmeticData n hn hns) (hp : p.Prime)
    (hodd : Odd p) (hpX : p ≤ X)
    (hno : ∀ q, q.Prime → Odd q → q ≤ X → q ∉ PrimeNeOneWitnessSet n) :
    bridge.character (p : ℤ) = 1 := by
  have hpdvd : ¬p ∣ n := not_dvd_of_no_primeNeOne_witness hp hodd hpX hno
  rw [bridge.character_eq]
  exact
    primitiveQuadraticCharacter_eq_one_of_no_primeNeOne_witness hn hp hodd
      hpX hno hpdvd

/--
Input/assumptions: the same bridge and no-witness cutoff as the preceding adapter.
Conclusion: the primitive normalization of the bridge character is one at every odd prime at or
below the cutoff.
Content: this is the dependent-level adapter needed by analytic APIs, whose arguments are written
with `χ.primitiveCharacter` rather than with the bridge's level character.
Proof: the bridge conductor divides `4*n`; an odd prime not dividing `n` is therefore coprime to
that conductor.  The primitive-character coprime evaluation then reduces to the preceding adapter.
Role: transports the no-witness value-one condition through primitive normalization.
-/
theorem JacobiCharacterArithmeticData.primitiveCharacter_eq_one_of_no_primeNeOne_witness {n X p : ℕ}
    {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : JacobiCharacterArithmeticData n hn hns) (hp : p.Prime)
    (hodd : Odd p) (hpX : p ≤ X)
    (hno : ∀ q, q.Prime → Odd q → q ≤ X → q ∉ PrimeNeOneWitnessSet n) :
    bridge.character.primitiveCharacter (p : ℤ) = 1 := by
  have hpdvd : ¬p ∣ n := not_dvd_of_no_primeNeOne_witness hp hodd hpX hno
  have hcdvd : bridge.character.conductor ∣ 4 * n := by
    rw [bridge.character_eq]
    exact primitiveQuadraticCharacter_conductor_dvd_level n hn
  have hprim :
    bridge.character.conductor =
      (complexQuadraticCharacter n hn).conductor :=
    (DirichletCharacter.isPrimitive_def bridge.character).mp bridge.character_primitive
  have hp4 : ¬p ∣ 4 := by
    intro hp4
    have hp2pow : p ∣ 2 ^ 2 := by simpa only [Nat.reducePow] using hp4
    have hp2 : p ∣ 2 := hp.dvd_of_dvd_pow hp2pow
    rcases (Nat.dvd_prime (by decide : Nat.Prime 2)).mp hp2 with hp1 | hp2
    · exact hp.ne_one hp1
    · have hne : p ≠ 2 := by
        intro heq
        subst p
        obtain ⟨k, hk⟩ := hodd
        omega
      exact hne hp2
  have hpc : ¬p ∣ (complexQuadraticCharacter n hn).conductor := by
    intro hpc
    rw [← hprim] at hpc
    have hp4n : p ∣ 4 * n := Nat.dvd_trans hpc hcdvd
    rcases (Nat.Prime.dvd_mul hp).mp hp4n with hp4' | hpn
    · exact hp4 hp4'
    · exact hpdvd hpn
  have hcop :
    IsCoprime (p : ℤ)
      ((complexQuadraticCharacter n hn).conductor : ℤ) := by
    exact_mod_cast hp.coprime_iff_not_dvd.mpr hpc
  rw [DirichletCharacter.primitiveCharacter_apply_of_isCoprime (χ := bridge.character) hcop]
  exact bridge.character_eq_one_of_no_primeNeOne_witness hp hodd hpX hno

/-- Transfer the even parity of the bridge character to its primitive normalization. -/
theorem JacobiCharacterArithmeticData.primitiveCharacter_even {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} (bridge : JacobiCharacterArithmeticData n hn hns) :
    bridge.character.primitiveCharacter.Even := by
  unfold DirichletCharacter.Even
  have hcop :
    IsCoprime (-1 : ℤ)
      ((complexQuadraticCharacter n hn).conductor : ℤ) := by
    refine ⟨-1, 0, by ring⟩
  have h :=
    DirichletCharacter.primitiveCharacter_apply_of_isCoprime (χ := bridge.character) (a := (-1 : ℤ))
      hcop
  have heven := bridge.character_even
  change
    bridge.character
        (-1 : ZMod (complexQuadraticCharacter n hn).conductor) =
      1 at heven
  have heven' :
    bridge.character
        ((-1 : ℤ) : ZMod (complexQuadraticCharacter n hn).conductor) =
      1 := by
    simpa only [Int.cast_neg, Int.cast_one] using heven
  have h' : bridge.character.primitiveCharacter ((-1 : ℤ) : ZMod bridge.character.conductor) = 1 :=
    h.trans heven'
  simpa only [Int.cast_neg, Int.cast_one] using h'

/--
Input/assumptions: a bridge whose character conductor is nonzero.
Conclusion: the primitive normalization of the bridge character is quadratic.
Content: every element is represented by its natural-number residue.  On the coprime branch,
`primitiveCharacter_apply_of_isCoprime` transfers the three-valued property; on the other branch,
`apply_eq_zero_iff` gives the zero value.  A local `NeZero` instance is transported across the
primitive conductor equality.
Proof: isolate the residue `av := a.val` before rewriting the conductor equality, which avoids an
ill-typed dependent rewrite of the `ZMod` domain.
Role: certifies the three-valued property after primitive normalization.
-/
theorem JacobiCharacterArithmeticData.primitiveCharacter_isQuadratic {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} [NeZero (complexQuadraticCharacter n hn).conductor]
    (bridge : JacobiCharacterArithmeticData n hn hns) :
    bridge.character.primitiveCharacter.IsQuadratic := by
  have hprim :
    bridge.character.conductor =
      (complexQuadraticCharacter n hn).conductor :=
    (DirichletCharacter.isPrimitive_def bridge.character).mp bridge.character_primitive
  let _ : NeZero bridge.character.conductor :=
    ⟨by
      intro hc
      exact
        (inferInstance :
              NeZero (complexQuadraticCharacter n hn).conductor).out
          (hprim ▸ hc)⟩
  intro a
  let av : ℕ := a.val
  by_cases hcop : Nat.Coprime av bridge.character.conductor
  · have hav : av = a.val := rfl
    have hcop' : Nat.Coprime av bridge.character.conductor := hav ▸ hcop
    have hcopq :
      Nat.Coprime av (complexQuadraticCharacter n hn).conductor :=
      hprim ▸ hcop'
    have hcopz :
      IsCoprime (av : ℤ)
        ((complexQuadraticCharacter n hn).conductor : ℤ) := by
      exact_mod_cast hcopq
    have happly :=
      DirichletCharacter.primitiveCharacter_apply_of_isCoprime (χ := bridge.character) (a :=
        (av : ℤ)) hcopz
    have hchar :=
      bridge.character_quadratic
        (((av : ℤ) : ZMod (complexQuadraticCharacter n hn).conductor))
    rcases hchar with hzero | hone | hneg
    · exact
        Or.inl
          (by
            simpa only [ZMod.natCast_val, ZMod.intCast_cast, ZMod.cast_id', id_eq, av] using
              happly.trans hzero)
    · exact
        Or.inr
          (Or.inl
            (by
              simpa only [ZMod.natCast_val, ZMod.intCast_cast, ZMod.cast_id', id_eq, av] using
                happly.trans hone))
    · exact
        Or.inr
          (Or.inr
            (by
              simpa only [ZMod.natCast_val, ZMod.intCast_cast, ZMod.cast_id', id_eq, av] using
                happly.trans hneg))
  · have hzero : bridge.character.primitiveCharacter (av : ℤ) = 0 :=
      (DirichletCharacter.apply_eq_zero_iff bridge.character.primitiveCharacter (av : ℤ)).mpr
        (by simpa only [Nat.isCoprime_iff_coprime] using hcop)
    exact
      Or.inl
        (by simpa only [ZMod.natCast_val, ZMod.intCast_cast, ZMod.cast_id', id_eq, av] using hzero)

/-- The primitive character has the three possible values at the prime `2`. -/
theorem primitiveQuadraticCharacter_two_value (n : ℕ) (hn : Odd n) :
    primitiveQuadraticCharacter n hn
          (2 : ZMod (complexQuadraticCharacter n hn).conductor) =
        0 ∨
      primitiveQuadraticCharacter n hn
          (2 : ZMod (complexQuadraticCharacter n hn).conductor) =
        1 ∨
      primitiveQuadraticCharacter n hn
          (2 : ZMod (complexQuadraticCharacter n hn).conductor) =
        -1 := by
  classical
  by_cases ha :
    IsUnit (2 : ZMod (complexQuadraticCharacter n hn).conductor)
  · rcases ha with ⟨u, hu⟩
    right
    have hsq :
      (primitiveQuadraticCharacter n hn
            (↑u : ZMod (complexQuadraticCharacter n hn).conductor)) ^
          2 =
        1 := by
      rw [← MulChar.pow_apply_coe]
      rw [(primitiveQuadraticCharacter_isQuadratic n hn).sq_eq_one]
      exact MulChar.one_apply_coe u
    rw [← hu]
    exact sq_eq_one_iff.mp hsq
  · left
    exact MulChar.map_nonunit (primitiveQuadraticCharacter n hn) ha

/-- A value `-1` at `2` forces the primitive conductor to be odd. -/
theorem primitiveQuadraticCharacter_conductor_odd_of_two_eq_neg_one (n : ℕ) (hn : Odd n)
    (hc :
      primitiveQuadraticCharacter n hn
          (2 : ZMod (complexQuadraticCharacter n hn).conductor) =
        -1) :
    Odd (complexQuadraticCharacter n hn).conductor := by
  by_contra hodd
  have heven : Even (complexQuadraticCharacter n hn).conductor :=
    Nat.not_odd_iff_even.mp hodd
  obtain ⟨k, hk⟩ := heven
  have hcop :
    ¬Nat.Coprime 2 (complexQuadraticCharacter n hn).conductor := by
    intro hcop
    have hodd' : Odd (complexQuadraticCharacter n hn).conductor :=
      Nat.Coprime.odd_of_left hcop
    obtain ⟨j, hj⟩ := hodd'
    omega
  have hunit :
    ¬IsUnit (2 : ZMod (complexQuadraticCharacter n hn).conductor) := by
    intro hunit
    exact
      hcop
        ((ZMod.isUnit_iff_coprime 2
              (complexQuadraticCharacter n hn).conductor).mp
          hunit)
  have hz := MulChar.map_nonunit (primitiveQuadraticCharacter n hn) hunit
  rw [hc] at hz
  norm_num only at hz

/-- Character value `-1` at `2` gives `D ≤ n` once the conductor is identified with `D`. -/
theorem JacobiCharacterArithmeticData.discriminant_le_of_two_eq_neg_one {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} (bridge : JacobiCharacterArithmeticData n hn hns)
    (hcond :
      (complexQuadraticCharacter n hn).conductor = bridge.discriminant)
    (hc :
      bridge.character
          (2 : ZMod (complexQuadraticCharacter n hn).conductor) =
        -1) :
    bridge.discriminant ≤ n := by
  have hcprim :
    primitiveQuadraticCharacter n hn
        (2 : ZMod (complexQuadraticCharacter n hn).conductor) =
      -1 := by
    rw [← bridge.character_eq]
    exact hc
  have hoddD : Odd bridge.discriminant := by
    rw [← hcond]
    exact
      primitiveQuadraticCharacter_conductor_odd_of_two_eq_neg_one n hn
        hcprim
  have hdmod : bridge.squarefreePart % 4 = 1 := by
    by_contra hdmod
    have hDfour : bridge.discriminant = 4 * bridge.squarefreePart := by
      rw [bridge.discriminant_eq]
      exact positiveFundamentalDiscriminant_eq_four_mul hdmod
    rw [hDfour] at hoddD
    obtain ⟨k, hk⟩ := hoddD
    omega
  exact bridge.discriminant_le_of_mod_four_eq_one hdmod

/-- If the conductor equals the discriminant and the character takes value `1` at `2`,
the discriminant is at most `n`. The proof forces the conductor to be odd and applies
the odd-discriminant bound. -/
theorem JacobiCharacterArithmeticData.discriminant_le_of_two_eq_one {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} (bridge : JacobiCharacterArithmeticData n hn hns)
    (hcond :
      (complexQuadraticCharacter n hn).conductor = bridge.discriminant)
    (hc :
      bridge.character
          (2 : ZMod (complexQuadraticCharacter n hn).conductor) =
        1) :
    bridge.discriminant ≤ n := by
  have hcprim :
    primitiveQuadraticCharacter n hn
        (2 : ZMod (complexQuadraticCharacter n hn).conductor) =
      1 := by
    rw [← bridge.character_eq]
    exact hc
  have hoddC : Odd (complexQuadraticCharacter n hn).conductor := by
    by_contra hodd
    have heven : Even (complexQuadraticCharacter n hn).conductor :=
      Nat.not_odd_iff_even.mp hodd
    obtain ⟨k, hk⟩ := heven
    have hcop :
      ¬Nat.Coprime 2 (complexQuadraticCharacter n hn).conductor := by
      intro hcop
      have hodd' : Odd (complexQuadraticCharacter n hn).conductor :=
        Nat.Coprime.odd_of_left hcop
      obtain ⟨j, hj⟩ := hodd'
      omega
    have hunit :
      ¬IsUnit (2 : ZMod (complexQuadraticCharacter n hn).conductor) := by
      intro hunit
      exact
        hcop
          ((ZMod.isUnit_iff_coprime 2
                (complexQuadraticCharacter n hn).conductor).mp
            hunit)
    have hz := MulChar.map_nonunit (primitiveQuadraticCharacter n hn) hunit
    rw [hcprim] at hz
    norm_num only at hz
  have hdmod : bridge.squarefreePart % 4 = 1 := by
    by_contra hdmod
    have hDfour : bridge.discriminant = 4 * bridge.squarefreePart := by
      rw [bridge.discriminant_eq]
      exact positiveFundamentalDiscriminant_eq_four_mul hdmod
    rw [hDfour] at hcond
    obtain ⟨k, hk⟩ := hoddC
    omega
  exact bridge.discriminant_le_of_mod_four_eq_one hdmod

/-- The Jacobi value is one whenever an odd prime is not a `≠ 1` witness. -/
theorem jacobiSym_eq_one_of_not_mem_primeNeOneWitnessSet {n p : ℕ} (hp : p.Prime) (_hodd : Odd p)
    (hmem : p ∉ PrimeNeOneWitnessSet n) : jacobiSym n p = 1 := by
  by_contra hne
  exact hmem ⟨hp, _hodd, hne⟩

end PseudoPrime.NumberTheory
