/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PseudoSquare.QNeOneDeciShiftBounds
public import PseudoPrime.LLS.Extensions.QNeOneScaleReciprocalComparison

/-! # Conditional Jacobi witnesses retaining the scale-dependent reciprocal error -/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- For an odd nonsquare arithmetic bridge under GRH, a root at least eight
and the scale-dependent separation contradict absence of non-one witnesses.
Pass the exact even reciprocal error through the three primitive values at two.
This connects the numerical condition to the actual quadratic character. -/
theorem qNeOneAnalyticFalse_of_scale_error {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    [NeZero (NumberTheory.complexQuadraticCharacter n hn).conductor]
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ} (hy : (8 : ℝ) ≤ y)
    (hsep :
      LLS.Extensions.qNeOneReciprocalUpper y (bridge.y + Real.log 4 - Real.log Real.pi)
          (LLS.Extensions.qNeOneScaleReciprocalLoss y) (Real.log 2) <
        LLS.Extensions.qNeOneReciprocalLower y)
    (hno : ∀ p, p.Prime → Odd p → p ≤ ⌊y ^ 2⌋₊ → p ∉ NumberTheory.primeNeOneWitnessSet n) :
    False := by
  let _ : NeZero bridge.character.conductor :=
    ⟨by
      intro hc
      exact
        (inferInstance : NeZero (NumberTheory.complexQuadraticCharacter n hn).conductor).out
          ((DirichletCharacter.isPrimitive_def bridge.character).mp bridge.character_primitive ▸
            hc)⟩
  have hodd : LLS.Extensions.OddPrimeTrivial bridge.character (y ^ 2) :=
    bridge.primitiveCharacter_eq_one_in_log_square_range (show 1 ≤ y by linarith only [hy]) hno
  have hcases :=
    NumberTheory.isQuadratic_primitiveCharacter bridge.character bridge.character_quadratic
      (2 : ZMod bridge.character.conductor)
  exact
    LLS.Extensions.not_oddPrimeTrivial_of_scale_reciprocal_separation bridge.character
      bridge.character_ne_one bridge.primitiveCharacter_even hGRH hy
      bridge.log_character_conductor_le_y_add_log_four
      (qNeOne_log_conductor_le_y_of_two_ne_zero bridge) hcases hsep hodd

/-- Under GRH and the stated scale-dependent separation, an odd-prime
Jacobi non-one witness exists through y squared. Negate existence and apply
the bridge contradiction. Zero Jacobi values are allowed.
This is a conditional witness theorem, without a new concrete entrance. -/
theorem exists_prime_ne_one_witness_le_of_scale_error {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    [NeZero (NumberTheory.complexQuadraticCharacter n hn).conductor]
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ} (hy : (8 : ℝ) ≤ y)
    (hsep :
      LLS.Extensions.qNeOneReciprocalUpper y (bridge.y + Real.log 4 - Real.log Real.pi)
          (LLS.Extensions.qNeOneScaleReciprocalLoss y) (Real.log 2) <
        LLS.Extensions.qNeOneReciprocalLower y) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ y ^ 2 ∧ jacobiSym n p ≠ 1 := by
  by_contra h
  apply qNeOneAnalyticFalse_of_scale_error bridge hGRH hy hsep
  intro p hp ho hb hmem
  apply h
  exact ⟨p, hp, ho, (Nat.floor_le (sq_nonneg y)).trans' (Nat.cast_le.mpr hb), hmem.2.2⟩

end PseudoPrime.PseudoSquare
