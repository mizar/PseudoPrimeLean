/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.PseudoSquare.Computation.QNeOneFiniteLogSq
import PseudoPrime.LLS.Extensions.QNeOneLogWeightedBounds
import PseudoPrime.PseudoSquare.QNeOneConcrete

/-!
# The integrated Q-ne-one witness bound

This file combines the finite CRT certificate, the three small squarefree parts, and the
analytic cutoff.  The squarefree transfer is kept explicit so that the finite and analytic
branches use the same witness notion.
-/

namespace PseudoPrime.PseudoSquare

/-!
Input/assumptions: GRH, an odd nonsquare `n ≥ 11`.
Conclusion: the least odd-prime Jacobi `≠ 1` witness for `n` is at most `(log n)^2`.
Content: dispatch the three small squarefree parts, the finite CRT range, and the analytic
cutoff; transfer the finite squarefree witness back to `n`.
Proof: the analytic branch is obtained by contradiction from the no-witness hypothesis.
Role: the interface consumed by the later `QNeOne` maximum theorem.
-/

theorem exists_primeNeOneWitness_cast_le_log_sq_of_odd_nonsquare
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hn11 : 11 ≤ n) :
    ∃ hdn : (NumberTheory.PrimeNeOneWitnessSet n).Nonempty,
      (NumberTheory.primeNeOneWitness n hdn : ℝ) ≤ (Real.log n) ^ 2 := by
  let bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns :=
    Classical.choice
      (NumberTheory.exists_jacobiCharacterArithmeticData (by omega) hn hns)
  have hbpos : 0 < bridge.squareFactor := Odd.pos bridge.squareFactor_odd
  have hb2pos : 0 < bridge.squareFactor ^ 2 := pow_pos hbpos 2
  by_cases hdsmall :
    bridge.squarefreePart = 3 ∨ bridge.squarefreePart = 5 ∨ bridge.squarefreePart = 7
  · exact
      NumberTheory.exists_primeNeOneWitness_cast_le_log_sq_of_small_squarefreePart
        bridge hn11 hdsmall
  by_cases hdbig : 1000000 ≤ bridge.squarefreePart
  · by_contra hbound
    have hno :
      ∀ q,
        q.Prime →
          Odd q → q ≤ ⌊bridge.y ^ 2⌋₊ → q ∉ NumberTheory.PrimeNeOneWitnessSet n := by
      intro q hq hqodd hqX hqmem
      have hleq :=
        NumberTheory.primeNeOneWitness_le n
          (NumberTheory.primeNeOneWitnessSet_nonempty_of_negOne
            (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns))
          hqmem
      have hqRfloor : (q : ℝ) ≤ (⌊bridge.y ^ 2⌋₊ : ℝ) := by exact_mod_cast hqX
      have hqR : (q : ℝ) ≤ bridge.y ^ 2 := hqRfloor.trans (Nat.floor_le (sq_nonneg _))
      have hdnR :
        (NumberTheory.primeNeOneWitness n
              (NumberTheory.primeNeOneWitnessSet_nonempty_of_negOne
                (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns)) :
            ℝ) ≤
          (Real.log n) ^ 2 := by
        have hleqR :
          (NumberTheory.primeNeOneWitness n
                (NumberTheory.primeNeOneWitnessSet_nonempty_of_negOne
                  (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn
                    hns)) :
              ℝ) ≤
            q := by
          exact_mod_cast hleq
        have hdle : bridge.squarefreePart ≤ n := by
          calc
            bridge.squarefreePart ≤ bridge.squareFactor ^ 2 * bridge.squarefreePart := by
              simpa only [Nat.mul_comm] using Nat.le_mul_of_pos_right bridge.squarefreePart hb2pos
            _ = n := bridge.squarefreePart_sq_mul
        have hyn : bridge.y ≤ Real.log n := by
          dsimp only [NumberTheory.JacobiCharacterArithmeticData.y]
          apply Real.strictMonoOn_log.monotoneOn
          · change (0 : ℝ) < (bridge.squarefreePart : ℝ)
            exact_mod_cast bridge.squarefreePart_pos
          · change (0 : ℝ) < (n : ℝ)
            exact_mod_cast (by omega)
          · exact_mod_cast hdle
        have hlogd : 0 ≤ bridge.y := by
          dsimp only [NumberTheory.JacobiCharacterArithmeticData.y]
          apply Real.log_nonneg
          exact_mod_cast (show 1 ≤ bridge.squarefreePart by omega)
        have hlogn : 0 ≤ Real.log (n : ℝ) := by
          apply Real.log_nonneg
          exact_mod_cast (show 1 ≤ n by omega)
        nlinarith only [hleqR, hqR, hyn, hlogd, hlogn]
      exact hbound ⟨_, hdnR⟩
    exact qNeOneAnalyticFalse_of_bridge_of_explicit_cutoff bridge hGRH hdbig hno
  · have hdbelow : bridge.squarefreePart < 1000000 := by omega
    have hd11 : 11 ≤ bridge.squarefreePart :=
      NumberTheory.JacobiCharacterArithmeticData.squarefreePart_ge_eleven_of_not_small
        bridge (by omega) (by omega) (by omega)
    have hnsd : ¬IsSquare bridge.squarefreePart := by
      rintro ⟨k, hk⟩
      apply hns
      refine ⟨bridge.squareFactor * k, ?_⟩
      calc
        n = bridge.squareFactor ^ 2 * bridge.squarefreePart := bridge.squarefreePart_sq_mul.symm
        _ = bridge.squareFactor ^ 2 * (k ^ 2) := by
          rw [hk]
          simp only [pow_two]
        _ = bridge.squareFactor * k * (bridge.squareFactor * k) := by ring
    let hdn : (NumberTheory.PrimeNeOneWitnessSet bridge.squarefreePart).Nonempty :=
      NumberTheory.primeNeOneWitnessSet_nonempty_of_negOne
        (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare
          bridge.squarefreePart_odd hnsd)
    have hwd :=
      primeNeOneWitness_cast_le_log_sq_of_eleven_le_of_lt_million (n := bridge.squarefreePart)
        bridge.squarefreePart_odd hnsd hd11 hdbelow
    let hdnN : (NumberTheory.PrimeNeOneWitnessSet n).Nonempty := by
      obtain ⟨p, hp⟩ := hdn
      exact ⟨p, NumberTheory.primeNeOneWitness_mem_of_squarefreePart_mem bridge hp⟩
    refine ⟨hdnN, ?_⟩
    have htransfer :=
      NumberTheory.primeNeOneWitness_le_of_squarefreePart bridge (hd := hdn)
    have htransferR :
      (NumberTheory.primeNeOneWitness n hdnN : ℝ) ≤
        (NumberTheory.primeNeOneWitness bridge.squarefreePart hdn : ℝ) := by
      exact_mod_cast htransfer
    have hdle : bridge.squarefreePart ≤ n := by
      calc
        bridge.squarefreePart ≤ bridge.squareFactor ^ 2 * bridge.squarefreePart := by
          simpa only [Nat.mul_comm] using Nat.le_mul_of_pos_right bridge.squarefreePart hb2pos
        _ = n := bridge.squarefreePart_sq_mul
    have hlog : Real.log (bridge.squarefreePart : ℝ) ≤ Real.log (n : ℝ) := by
      apply Real.strictMonoOn_log.monotoneOn
      · change (0 : ℝ) < (bridge.squarefreePart : ℝ)
        exact_mod_cast bridge.squarefreePart_pos
      · change (0 : ℝ) < (n : ℝ)
        exact_mod_cast (by omega)
      · exact_mod_cast hdle
    have hlogd : 0 ≤ Real.log (bridge.squarefreePart : ℝ) := by
      apply Real.log_nonneg
      exact_mod_cast (show 1 ≤ bridge.squarefreePart by omega)
    have hlogn : 0 ≤ Real.log (n : ℝ) := by
      apply Real.log_nonneg
      exact_mod_cast (show 1 ≤ n by omega)
    nlinarith only [hwd, htransferR, hlog, hlogd, hlogn]

end PseudoPrime.PseudoSquare
