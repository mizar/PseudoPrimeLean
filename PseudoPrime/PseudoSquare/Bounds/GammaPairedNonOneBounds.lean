/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PseudoSquare.Bounds.GammaNegativeNearSquareBounds

/-! # Non-one witnesses and full maxima from the paired negative comparison -/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- Under GRH for an odd nonsquare n and common endpoint L at least 700
with log n at most L, the least non-one witness is at most (99/100)L squared.
Compare it with the negative witness at that same endpoint.
This covers small inputs and supplies full-domain finite maxima. -/
theorem primeNeOneWitness_cast_le_paired_nearSquare_endpoint
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) {L : ℝ} (hL : 700 ≤ L) (hlogn : Real.log n ≤ L)
    (hw : (NumberTheory.primeNeOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNeOneWitness n hw : ℝ) ≤ (99 / 100 : ℝ) * L ^ 2 := by
  let hneg := NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns
  have hc := NumberTheory.primeNeOneWitness_le_primeNegOneWitness n hneg
  have hb := primeNegOneWitness_cast_le_paired_nearSquare_endpoint hGRH hn hns hL hlogn hneg
  exact (Nat.cast_le.mpr hc).trans hb

/-- Under GRH, every odd nonsquare n with log n at least 700 has an odd
prime non-one witness through (99/100)(log n) squared.
Use the proved negative witness and its value -1.
This strengthens the coefficient entrance without a new dyadic split. -/
theorem exists_prime_ne_one_witness_le_nearSquare_gamma_log_700
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hL : 700 ≤ Real.log n) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ (99 / 100 : ℝ) * (Real.log n) ^ 2 ∧ jacobiSym n p ≠ 1 := by
  obtain ⟨p, hp, ho, hb, hv⟩ :=
    exists_prime_neg_one_witness_le_nearSquare_gamma_log_700 hGRH hn hns hL
  refine ⟨p, hp, ho, hb, ?_⟩
  rw [hv]
  norm_num only

/-- Under GRH and log B at least 700, the full finite maximum QNeOne B
is at most (99/100)(log B) squared. Compare with QNegOne B before applying
the common-endpoint negative bound. No input in the admissible domain is
discarded, and no new finite certificate is used. -/
theorem QNeOne_le_nearSquare_gamma_log_700 {B : ℕ} (hB : 700 ≤ Real.log B)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    (QNeOne B : ℝ) ≤ (99 / 100 : ℝ) * (Real.log B) ^ 2 := by
  exact (Nat.cast_le.mpr (QNeOne_le_QNegOne B)).trans (QNegOne_le_nearSquare_gamma_log_700 hB hGRH)

end PseudoPrime.PseudoSquare
