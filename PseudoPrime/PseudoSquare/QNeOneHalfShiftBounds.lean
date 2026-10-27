/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PseudoSquare.QNeOneScaleErrorBounds
public import PseudoPrime.LLS.Extensions.QNeOneHalfShiftSeparation

/-! # One-half root saving for odd-prime Jacobi non-one witnesses -/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- Under GRH, for odd nonsquare n with log n<=L and L>=25/2, an odd-prime
non-one Jacobi witness lies through (L-1/2)^2. Apply the analytic comparison
to the arithmetic bridge at this common root. All squarefree parts are covered;
no finite-input theorem is needed to handle smaller parts. -/
theorem exists_prime_ne_one_witness_le_half_endpoint {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    {L : ℝ} (hL : (25 / 2 : ℝ) ≤ L) (hlogn : Real.log n ≤ L)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ (L - 1 / 2) ^ 2 ∧ jacobiSym n p ≠ 1 := by
  let : NeZero (NumberTheory.complexQuadraticCharacter n hn).conductor :=
    ⟨NumberTheory.complexQuadraticCharacter_conductor_ne_zero n hn⟩
  obtain ⟨bridge⟩ := NumberTheory.exists_jacobiCharacterArithmeticData (Odd.pos hn) hn hns
  have hy : (12 : ℝ) ≤ L - 1 / 2 := by linarith only [hL]
  have h8 : (8 : ℝ) ≤ L - 1 / 2 := by linarith only [hy]
  have hlev : bridge.y ≤ (L - 1 / 2) + 1 / 2 := by
    linarith only [(qNeOne_bridge_y_le_log_input bridge).trans hlogn]
  have hsep := LLS.Extensions.qNeOneHalfShiftUpper_lt_lower hy hlev
  exact
    exists_prime_ne_one_witness_le_of_scale_error bridge hGRH h8
      ((LLS.Extensions.qNeOneScaleReciprocalUpper_le_retained h8).trans_lt hsep)

/-- Under the common-endpoint assumptions, the least odd-prime non-one
witness is at most (L-1/2)^2. Compare it with the endpoint witness.
This supplies the full finite-maximum interface. -/
theorem primeNeOneWitness_cast_le_half_endpoint
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) {L : ℝ} (hL : (25 / 2 : ℝ) ≤ L) (hlogn : Real.log n ≤ L)
    (hw : (NumberTheory.primeNeOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNeOneWitness n hw : ℝ) ≤ (L - 1 / 2) ^ 2 := by
  obtain ⟨p, hp, ho, hb, hv⟩ := exists_prime_ne_one_witness_le_half_endpoint hn hns hL hlogn hGRH
  exact (Nat.cast_le.mpr (NumberTheory.primeNeOneWitness_le n hw ⟨hp, ho, hv⟩)).trans hb

/-- Under GRH for odd nonsquare n with log n>=25/2, an odd-prime witness
has Jacobi value not one and lies through (log n-1/2)^2, strictly below log(n)^2.
Specialize the common endpoint and compare the squares. Zero values are allowed. -/
theorem exists_prime_ne_one_witness_le_half_shift_and_lt_log_sq
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hL : (25 / 2 : ℝ) ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        Odd p ∧
        (p : ℝ) ≤ (Real.log n - 1 / 2) ^ 2 ∧ (p : ℝ) < (Real.log n) ^ 2 ∧ jacobiSym n p ≠ 1 := by
  obtain ⟨p, hp, ho, hb, hv⟩ :=
    exists_prime_ne_one_witness_le_half_endpoint hn hns hL (le_refl _) hGRH
  have hs : (Real.log n - 1 / 2) ^ 2 < (Real.log n) ^ 2 := by nlinarith only [hL]
  exact ⟨p, hp, ho, hb, hb.trans_lt hs, hv⟩

/-- Under GRH and log B>=25/2, the full maximum of least non-one witnesses
through B is at most (log B-1/2)^2. Apply the common endpoint to every admissible
input, including small inputs. This uses no new finite input certificates. -/
theorem QNeOne_le_half_shift {B : ℕ} (hL : (25 / 2 : ℝ) ≤ Real.log B)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    (QNeOne B : ℝ) ≤ (Real.log B - 1 / 2) ^ 2 := by
  apply QNeOne_cast_le_of_forall (sq_nonneg _)
  intro n hn
  have ha := NumberTheory.mem_admissibleFinset_iff.mp hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Odd.pos ha.odd
  have hnB : (n : ℝ) ≤ B := by exact_mod_cast ha.le
  exact
    primeNeOneWitness_cast_le_half_endpoint hGRH ha.odd ha.not_isSquare hL (Real.log_le_log hn0 hnB)
      (NumberTheory.primeNeOneWitnessSet_nonempty_of_negOne
        (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare ha.odd ha.not_isSquare))

/-- For L>=25/2, the half-shift square is smaller than the one-tenth square.
Rational arithmetic compares the roots. This records the improvement on their
common domain without combining the bounds by a minimum function. -/
theorem half_shift_sq_lt_deci_shift {L : ℝ} (hL : (25 / 2 : ℝ) ≤ L) :
    (L - 1 / 2) ^ 2 < (L - 1 / 10) ^ 2 := by nlinarith only [hL]

end PseudoPrime.PseudoSquare
