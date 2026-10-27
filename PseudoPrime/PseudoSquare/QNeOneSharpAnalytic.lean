/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Extensions.QNeOneSharpCharacterBounds
public import PseudoPrime.NumberTheory.JacobiCharacterArithmetic

/-! # Quadratic non-one analytic witnesses from a smaller squarefree-part threshold -/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- Input: an odd nonsquare arithmetic bridge and a nonzero primitive value at two.
Claim: its log conductor is at most the logarithm of its squarefree part.
Proof: coprimality at two excludes the even fundamental discriminant branch.
This supplies the sharp conductor bound required by both unramified analytic branches. -/
theorem qNeOne_log_conductor_le_y_of_two_ne_zero {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    [NeZero (NumberTheory.complexQuadraticCharacter n hn).conductor]
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (h2 : bridge.character.primitiveCharacter 2 ≠ 0) :
    Real.log bridge.character.conductor ≤ bridge.y := by
  have hc : IsCoprime (2 : ℤ) (bridge.character.conductor : ℤ) := by
    by_contra h
    apply h2
    simpa only [Int.cast_ofNat] using
      (DirichletCharacter.apply_eq_zero_iff bridge.character.primitiveCharacter (2 : ℤ)).mpr h
  have hoddC : Odd bridge.character.conductor := Nat.Coprime.odd_of_left hc.natCoprime
  have hoddD : Odd bridge.discriminant := by
    rw [← bridge.character_conductor_eq_discriminant]
    exact hoddC
  have hdmod : bridge.squarefreePart % 4 = 1 := by
    by_contra h
    rw [bridge.discriminant_eq, NumberTheory.positiveFundamentalDiscriminant_eq_four_mul h] at hoddD
    exact (Nat.not_even_iff_odd.mpr hoddD) ⟨2 * bridge.squarefreePart, by ring⟩
  have hd : bridge.discriminant = bridge.squarefreePart := by
    rw [bridge.discriminant_eq, NumberTheory.positiveFundamentalDiscriminant_eq_self hdmod]
  exact bridge.log_character_conductor_le_of_discriminant_le hd.le

/-- Input: an odd nonsquare arithmetic bridge, GRH and log squarefree part at least 99/10.
Claim: absence of all odd-prime non-one witnesses through its logarithmic square is impossible.
Proof: derive the primitive odd-prime condition and apply the new three-branch contradiction.
This is the analytic no-witness elimination without a finite squarefree-part certificate. -/
theorem qNeOneAnalyticFalse_of_bridge_of_sharp {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    [NeZero (NumberTheory.complexQuadraticCharacter n hn).conductor]
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hy : (99 / 10 : ℝ) ≤ bridge.y)
    (hno : ∀ p, p.Prime → Odd p → p ≤ ⌊bridge.y ^ 2⌋₊ → p ∉ NumberTheory.primeNeOneWitnessSet n) :
    False := by
  let _ : NeZero bridge.character.conductor :=
    ⟨by
      intro hc
      exact
        (inferInstance : NeZero (NumberTheory.complexQuadraticCharacter n hn).conductor).out
          ((DirichletCharacter.isPrimitive_def bridge.character).mp bridge.character_primitive ▸
            hc)⟩
  have hodd : LLS.Extensions.OddPrimeTrivial bridge.character (bridge.y ^ 2) :=
    bridge.primitiveCharacter_eq_one_in_log_square_range (show 1 ≤ bridge.y by linarith only [hy])
      hno
  have hcases :=
    NumberTheory.isQuadratic_primitiveCharacter bridge.character bridge.character_quadratic
      (2 : ZMod bridge.character.conductor)
  exact
    LLS.Extensions.not_oddPrimeTrivial_of_sharp bridge.character bridge.character_ne_one
      bridge.primitiveCharacter_even hGRH hy bridge.log_character_conductor_le_y_add_log_four
      (qNeOne_log_conductor_le_y_of_two_ne_zero bridge) hcases hodd

/-- Input: the same arithmetic bridge and analytic lower threshold under GRH.
Claim: there is an actual odd-prime non-one witness through the squarefree logarithmic square.
Proof: negate witness existence and use the analytic contradiction.
This connects the real comparison to the original Jacobi symbol at n. -/
theorem exists_prime_ne_one_witness_le_log_squarefree_sq_of_sharp {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} [NeZero (NumberTheory.complexQuadraticCharacter n hn).conductor]
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hy : (99 / 10 : ℝ) ≤ bridge.y) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ bridge.y ^ 2 ∧ jacobiSym n p ≠ 1 := by
  by_contra h
  apply qNeOneAnalyticFalse_of_bridge_of_sharp bridge hGRH hy
  intro p hp ho hb hmem
  apply h
  exact ⟨p, hp, ho, (Nat.floor_le (sq_nonneg bridge.y)).trans' (Nat.cast_le.mpr hb), hmem.2.2⟩

/-- Input: a natural number at least 20000.
Claim: its logarithm is at least 99/10.
Proof: use the factorization of 20000 into powers of two and five and logarithm monotonicity.
This gives a small explicit integer start for the real analytic threshold. -/
theorem log_ge_ninety_nine_tenths_of_ge_20000 {d : ℕ} (hd : 20000 ≤ d) :
    (99 / 10 : ℝ) ≤ Real.log d := by
  have hbase : (99 / 10 : ℝ) ≤ Real.log 20000 := by
    rw [show (20000 : ℝ) = 2 ^ 5 * 5 ^ 4 by norm_num only,
      Real.log_mul (by norm_num only : (2 ^ 5 : ℝ) ≠ 0) (by norm_num only : (5 ^ 4 : ℝ) ≠ 0),
      Real.log_pow, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [Real.log_two_gt_d9, Real.log_five_gt_d9]
  exact hbase.trans (Real.log_le_log (by norm_num only) (Nat.cast_le.mpr hd))

/-- Input: an odd nonsquare arithmetic bridge with squarefree part at least 20000 and GRH.
Claim: an odd-prime non-one witness lies below its squarefree-part logarithmic square.
Proof: apply the analytic threshold conversion and the concrete witness theorem.
No finite input or small-squarefree-part case is used. -/
theorem exists_prime_ne_one_witness_le_log_squarefree_sq_of_ge_20000 {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} [NeZero (NumberTheory.complexQuadraticCharacter n hn).conductor]
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hd : 20000 ≤ bridge.squarefreePart) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ bridge.y ^ 2 ∧ jacobiSym n p ≠ 1 := by
  exact
    exists_prime_ne_one_witness_le_log_squarefree_sq_of_sharp bridge hGRH
      (log_ge_ninety_nine_tenths_of_ge_20000 hd)

/-- Input: an odd nonsquare bridge whose squarefree part is strictly below the input.
Claim: the squarefree logarithm is strictly below the input logarithm.
Proof: apply strict logarithm monotonicity to the positive squarefree part.
This yields a strict input bound when a nontrivial square factor is present. -/
theorem qNeOne_bridge_y_lt_log_of_squarefreePart_lt {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hdn : bridge.squarefreePart < n) : bridge.y < Real.log n := by
  exact Real.log_lt_log (Nat.cast_pos.mpr bridge.squarefreePart_pos) (Nat.cast_lt.mpr hdn)

/-- Input: GRH and a bridge with squarefree part at least 20000 but strictly below n.
Claim: an odd-prime non-one witness lies strictly below the input logarithmic square.
Proof: combine the analytic squarefree-part witness with strict logarithm monotonicity.
The squarefree-input boundary and small squarefree parts remain separate analytic tasks. -/
theorem exists_prime_ne_one_witness_lt_log_sq_of_squarefreePart_lt {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} [NeZero (NumberTheory.complexQuadraticCharacter n hn).conductor]
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hd : 20000 ≤ bridge.squarefreePart) (hdn : bridge.squarefreePart < n) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) < (Real.log n) ^ 2 ∧ jacobiSym n p ≠ 1 := by
  obtain ⟨p, hp, ho, hb, hv⟩ :=
    exists_prime_ne_one_witness_le_log_squarefree_sq_of_ge_20000 bridge hGRH hd
  have hy : 0 ≤ bridge.y :=
    (by norm_num only : (0 : ℝ) ≤ 99 / 10).trans (log_ge_ninety_nine_tenths_of_ge_20000 hd)
  have hlog := qNeOne_bridge_y_lt_log_of_squarefreePart_lt bridge hdn
  have hs := (sq_lt_sq₀ hy (hy.trans hlog.le)).mpr hlog
  exact ⟨p, hp, ho, hb.trans_lt hs, hv⟩

end PseudoPrime.PseudoSquare
