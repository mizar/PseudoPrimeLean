/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.RationalPoleSharpEntrance

/-! # Common-scale fourth-pole Jacobi witnesses

The selected fourth-pole kernel and finite scalar budget allow a common logarithmic upper
scale independent of the input's own logarithm. These application-specific bounds belong
with the LLS kernel and its numerical budget. Cumulative maxima and Selfridge transfers
remain in their consumer modules; no computational certificate depends on this proof layer.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- A free upper logarithmic scale yields an actual negative odd-prime Jacobi witness.
Input: arithmetic data, GRH, a scale at least ten to the eighteenth and an input below it.
Claim: the witness is below the selected coefficient times the squared scale.
Proof: bound conductor and level logarithms by the scale, then apply the scalar gap.
Role: eliminate artificial low-input history from cumulative fourth-pole bounds. -/
theorem fourPole_jacobi_common_scale {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {L : ℝ} (hL : (10 : ℝ) ^ 18 ≤ L)
    (hlog : Real.log n ≤ L) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ (777 / 1000 : ℝ) * L ^ 2 ∧ jacobiSym n p = -1 := by
  let : NeZero (4 * n) := ⟨(Nat.mul_pos (by norm_num only : (0 : ℕ) < 4) hn.pos).ne'⟩
  have hL2 : 2 ≤ L := by
    norm_num only at hL
    linarith only [hL]
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn.pos
  have hlog4 : Real.log (4 : ℝ) ≤ 2 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num only : (0 : ℝ) < 2)
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num only, Real.log_pow]
    norm_num only at h ⊢
    linarith only [h]
  have hG : Real.log (4 * (n : ℝ)) ≤ L + 2 := by
    rw [Real.log_mul (by norm_num only : (4 : ℝ) ≠ 0) hnR.ne']
    linarith only [hlog4, hlog]
  have hcon : (NumberTheory.complexQuadraticCharacter n hn).conductor ≤ 4 * n :=
    Nat.le_of_dvd (Nat.mul_pos (by norm_num only : (0 : ℕ) < 4) hn.pos)
      (DirichletCharacter.conductor_dvd_level (NumberTheory.complexQuadraticCharacter n hn))
  have hcon0 : 0 < (NumberTheory.complexQuadraticCharacter n hn).conductor :=
    Nat.pos_of_ne_zero (NumberTheory.complexQuadraticCharacter n hn).conductor_ne_zero
  have hF : Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor ≤ L + 2 := by
    have h := Real.log_le_log (Nat.cast_pos.mpr hcon0) (Nat.cast_le.mpr hcon)
    norm_num only [Nat.cast_mul, Nat.cast_ofNat] at h
    exact h.trans hG
  obtain ⟨hxl, _, _, _, _, _, _⟩ := fourPole_sharp_finite_scale_bounds hL2
  apply fourPole_exists_jacobi_scalar bridge hGRH (hL2.trans hxl)
  exact fourPole_sharp_finite_scalar_gap hL hF hG

/-- The common-scale witness needs no externally supplied arithmetic bridge.
Input: an odd nonsquare input, GRH, and a valid common logarithmic scale.
Claim: an actual member of the negative odd-prime witness set meets the scale bound.
Proof: construct the arithmetic data and apply the fourth-pole comparison.
Role: provide a closed public input to least-witness and cumulative consumers. -/
theorem fourPole_common_scale_witness {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {L : ℝ} (hL : (10 : ℝ) ^ 18 ≤ L)
    (hlog : Real.log n ≤ L) :
    ∃ p : ℕ, p ∈ NumberTheory.primeNegOneWitnessSet n ∧ (p : ℝ) ≤ (777 / 1000 : ℝ) * L ^ 2 :=
  Nonempty.elim (NumberTheory.exists_jacobiCharacterArithmeticData hn.pos hn hns) fun bridge ↦
    Exists.elim (fourPole_jacobi_common_scale bridge hGRH hL hlog) fun p hp ↦
      ⟨p, ⟨hp.1, hp.2.1, hp.2.2.2⟩, hp.2.2.1⟩

/-- The least actual negative odd-prime witness obeys the common-scale bound.
Input: an odd nonsquare input, GRH, the scale conditions, and witness-set nonemptiness.
Claim: the least witness is below the selected squared-scale bound.
Proof: minimize the supplied actual witness. Role: finite-maximum extraction. -/
theorem fourPole_common_scale_least {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {L : ℝ} (hL : (10 : ℝ) ^ 18 ≤ L)
    (hlog : Real.log n ≤ L) (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ (777 / 1000 : ℝ) * L ^ 2 :=
  Exists.elim (fourPole_common_scale_witness hn hns hGRH hL hlog) fun _p hp ↦
    (Nat.cast_le.mpr (NumberTheory.primeNegOneWitness_le n hw hp.1)).trans hp.2

end PseudoPrime.LLS.PaperStatements
