/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PseudoSquare.QNeOneHalfShiftBounds
public import PseudoPrime.LLS.Extensions.QNeOneLogShiftSeparation

/-! # Non-one witnesses with a negative logarithmic root correction -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For L>=16, the explicit radius L-log L+3 is at least twelve and satisfies
L<=y+log y-2. Apply logarithmic tangent bounds at sixteen and at y.
This converts the implicit analytic allowance into an elementary formula. -/
theorem qNeOneLogShiftRadius_properties {L : ℝ} (hL : (16 : ℝ) ≤ L) :
    12 ≤ L - Real.log L + 3 ∧ L ≤ (L - Real.log L + 3) + Real.log (L - Real.log L + 3) - 2 := by
  have hLp : 0 < L := by linarith only [hL]
  have ht := log_le_log_add_sub_div (by norm_num only : (0 : ℝ) < 16) hLp
  have h16 : Real.log 16 < (3 : ℝ) := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num only, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [Real.log_two_lt_d9]
  have hlog : Real.log L ≤ 2 + L / 16 := by linarith only [ht, h16]
  have hy : (12 : ℝ) ≤ L - Real.log L + 3 := by linarith only [hL, hlog]
  have hhalf : L ≤ 2 * (L - Real.log L + 3) := by linarith only [hL, hlog]
  have hyp : 0 < L - Real.log L + 3 := by linarith only [hy]
  have ht2 := log_le_log_add_sub_div hyp hLp
  have hratio : (L - (L - Real.log L + 3)) / (L - Real.log L + 3) ≤ 1 := by
    apply (div_le_one hyp).mpr
    linarith only [hhalf]
  exact ⟨hy, by linarith only [ht2, hratio]⟩

end PseudoPrime.Analysis

namespace PseudoPrime.PseudoSquare

/-- Under GRH for odd nonsquare n with log n<=L and L>=16, a non-one odd-prime
witness lies through (L-log L+3)^2. Insert the explicit radius into the variable
conductor comparison and arithmetic bridge. Small squarefree parts use the
same analytic endpoint, without additional finite-input certificates. -/
theorem exists_prime_ne_one_witness_le_log_shift_endpoint {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    {L : ℝ} (hL : (16 : ℝ) ≤ L) (hlogn : Real.log n ≤ L)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ (L - Real.log L + 3) ^ 2 ∧ jacobiSym n p ≠ 1 := by
  let : NeZero (NumberTheory.complexQuadraticCharacter n hn).conductor :=
    ⟨NumberTheory.complexQuadraticCharacter_conductor_ne_zero n hn⟩
  obtain ⟨bridge⟩ := NumberTheory.exists_jacobiCharacterArithmeticData (Odd.pos hn) hn hns
  have hroot := Analysis.qNeOneLogShiftRadius_properties hL
  have h8 : (8 : ℝ) ≤ L - Real.log L + 3 := by linarith only [hroot.1]
  have hlev := ((qNeOne_bridge_y_le_log_input bridge).trans hlogn).trans hroot.2
  have hsep := LLS.Extensions.qNeOneLogShiftUpper_lt_lower hroot.1 hlev
  exact
    exists_prime_ne_one_witness_le_of_scale_error bridge hGRH h8
      ((LLS.Extensions.qNeOneScaleReciprocalUpper_le_retained h8).trans_lt hsep)

/-- Under the common-endpoint assumptions, the least odd-prime non-one
Jacobi witness is bounded by the explicit logarithmic radius squared.
Compare it with the endpoint witness. This supplies the full-maximum interface. -/
theorem primeNeOneWitness_cast_le_log_shift_endpoint
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) {L : ℝ} (hL : (16 : ℝ) ≤ L) (hlogn : Real.log n ≤ L)
    (hw : (NumberTheory.primeNeOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNeOneWitness n hw : ℝ) ≤ (L - Real.log L + 3) ^ 2 := by
  obtain ⟨p, hp, ho, hb, hv⟩ :=
    exists_prime_ne_one_witness_le_log_shift_endpoint hn hns hL hlogn hGRH
  exact (Nat.cast_le.mpr (NumberTheory.primeNeOneWitness_le n hw ⟨hp, ho, hv⟩)).trans hb

/-- Under GRH and log B>=16, the full maximum of least non-one witnesses
through B is at most (log B-log log B+3)^2. Apply the common endpoint to every
admissible input. This includes small inputs through the same analytic proof. -/
theorem QNeOne_le_log_shift {B : ℕ} (hL : (16 : ℝ) ≤ Real.log B)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    (QNeOne B : ℝ) ≤ (Real.log B - Real.log (Real.log B) + 3) ^ 2 := by
  apply QNeOne_cast_le_of_forall (sq_nonneg _)
  intro n hn
  have ha := NumberTheory.mem_admissibleFinset_iff.mp hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Odd.pos ha.odd
  have hnB : (n : ℝ) ≤ B := by exact_mod_cast ha.le
  exact
    primeNeOneWitness_cast_le_log_shift_endpoint hGRH ha.odd ha.not_isSquare hL
      (Real.log_le_log hn0 hnB)
      (NumberTheory.primeNeOneWitnessSet_nonempty_of_negOne
        (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare ha.odd ha.not_isSquare))

/-- For L>=32 the explicit logarithmic radius squared is strictly below L^2.
Use the positive radius and log L>3. This distinguishes applicability from
strict improvement over the uncorrected square. -/
theorem log_shift_sq_lt_log_sq {L : ℝ} (hL : (32 : ℝ) ≤ L) : (L - Real.log L + 3) ^ 2 < L ^ 2 := by
  have h16 : (16 : ℝ) ≤ L := by linarith only [hL]
  have hy := (Analysis.qNeOneLogShiftRadius_properties h16).1
  have hlog : (3 : ℝ) < Real.log L := by
    have h32 : (3 : ℝ) < Real.log 32 := by
      rw [show (32 : ℝ) = 2 ^ 5 by norm_num only, Real.log_pow]
      norm_num only [Nat.cast_ofNat]
      linarith only [Real.log_two_gt_d9]
    exact h32.trans_le (Real.log_le_log (by norm_num only) hL)
  nlinarith only [hy, hlog, hL]

/-- Under GRH for odd nonsquare n with log n>=32, an odd-prime non-one witness
lies through the logarithmic radius squared and strictly below log(n)^2.
Combine the endpoint theorem and strict square comparison. Zero values are allowed. -/
theorem exists_prime_ne_one_witness_le_log_shift_and_lt_log_sq
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hL : (32 : ℝ) ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        Odd p ∧
        (p : ℝ) ≤ (Real.log n - Real.log (Real.log n) + 3) ^ 2 ∧
        (p : ℝ) < (Real.log n) ^ 2 ∧ jacobiSym n p ≠ 1 := by
  obtain ⟨p, hp, ho, hb, hv⟩ :=
    exists_prime_ne_one_witness_le_log_shift_endpoint hn hns
      (show (16 : ℝ) ≤ Real.log n by linarith only [hL]) (le_refl _) hGRH
  exact ⟨p, hp, ho, hb, hb.trans_lt (log_shift_sq_lt_log_sq hL), hv⟩

end PseudoPrime.PseudoSquare
