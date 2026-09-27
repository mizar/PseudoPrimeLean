/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.PrimeTestBounds.Selfridge.LogBounds
import PseudoPrime.PseudoSquare.Bounds.QNeOneLogSq
import PseudoPrime.PseudoSquare.Bounds.ElementaryOmegaFinal

/-!
# GRH Selfridge logarithmic bounds
-/

namespace PseudoPrime.PrimeTestBounds.Selfridge

theorem classicalFirstStopNeOne_cast_le_log_sq_of_49_le
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn49 : 49 ≤ n)
    (hn : Odd n) (hns : ¬IsSquare n) :
    (PrimeTest.firstStopNeOne PrimeTest.isClassicalCandidate n
          (PrimeTest.classicalFirstStopNeOneSet_nonempty_of_odd_nonsquare hn hns) :
        ℝ) ≤
      Real.log (n : ℝ) ^ 2 := by
  let hs := PrimeTest.classicalFirstStopNeOneSet_nonempty_of_odd_nonsquare hn hns
  obtain ⟨hw, hqR⟩ :=
    PseudoSquare.exists_primeNeOneWitness_cast_le_log_sq_of_odd_nonsquare hGRH hn hns (by omega)
  have hmax :=
    PrimeTest.primeNeOneWitness_le_classicalFirstStop_le_max_unconditional hn.pos hn hns hw hs
  have hmaxR :
    (PrimeTest.firstStopNeOne PrimeTest.isClassicalCandidate n hs : ℝ) ≤
      ((max 15 (NumberTheory.primeNeOneWitness n hw) : ℕ) : ℝ) := by
    exact_mod_cast hmax.2
  have hlog : (15 : ℝ) ≤ Real.log (n : ℝ) ^ 2 := (fifteen_lt_log_sq_of_forty_nine_le hn49).le
  have hmaxlog :
    ((max 15 (NumberTheory.primeNeOneWitness n hw) : ℕ) : ℝ) ≤ Real.log (n : ℝ) ^ 2 := by
    simpa only [Nat.cast_max, Nat.cast_ofNat] using (max_le hlog hqR)
  exact hmaxR.trans hmaxlog

theorem classicalSelfridgeD_firstStopNeOne_natAbs_cast_le_log_sq_of_49_le
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn49 : 49 ≤ n)
    (hn : Odd n) (hns : ¬IsSquare n) :
    ((PrimeTest.selfridgeD
            (PrimeTest.firstStopNeOne PrimeTest.isClassicalCandidate n
              (PrimeTest.classicalFirstStopNeOneSet_nonempty_of_odd_nonsquare hn hns))).natAbs :
        ℝ) ≤
      Real.log (n : ℝ) ^ 2 := by
  simpa only [PrimeTest.selfridgeD_natAbs] using
    classicalFirstStopNeOne_cast_le_log_sq_of_49_le hGRH hn49 hn hns

theorem classicalFirstStopNeOne_cast_le_log_sq_of_13_le
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn13 : 13 ≤ n)
    (hn : Odd n) (hns : ¬IsSquare n) :
    (PrimeTest.firstStopNeOne PrimeTest.isClassicalCandidate n
          (PrimeTest.classicalFirstStopNeOneSet_nonempty_of_odd_nonsquare hn hns) :
        ℝ) ≤
      Real.log (n : ℝ) ^ 2 := by
  by_cases hn49 : n < 49
  · exact classicalFirstStopNeOne_cast_le_log_sq_of_13_le_of_lt_49 hn13 hn49 hn hns
  · exact classicalFirstStopNeOne_cast_le_log_sq_of_49_le hGRH (by omega) hn hns

theorem classicalSelfridgeD_firstStopNeOne_natAbs_cast_le_log_sq_of_13_le
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn13 : 13 ≤ n)
    (hn : Odd n) (hns : ¬IsSquare n) :
    ((PrimeTest.selfridgeD
            (PrimeTest.firstStopNeOne PrimeTest.isClassicalCandidate n
              (PrimeTest.classicalFirstStopNeOneSet_nonempty_of_odd_nonsquare hn hns))).natAbs :
        ℝ) ≤
      Real.log (n : ℝ) ^ 2 := by
  simpa only [PrimeTest.selfridgeD_natAbs] using
    classicalFirstStopNeOne_cast_le_log_sq_of_13_le hGRH hn13 hn hns

theorem wheel30SelfridgeD_firstStopNeOne_natAbs_cast_le_log_sq_of_13_le
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn13 : 13 ≤ n)
    (hn : Odd n) (hns : ¬IsSquare n) :
    ((PrimeTest.selfridgeD
            (PrimeTest.firstStopNeOne PrimeTest.isWheel30NeOneCandidate n
              (PrimeTest.wheel30FirstStopNeOneSet_nonempty_of_odd_nonsquare hn hns))).natAbs :
        ℝ) ≤
      Real.log (n : ℝ) ^ 2 := by
  let hclass := PrimeTest.classicalFirstStopNeOneSet_nonempty_of_odd_nonsquare hn hns
  let hwheel := PrimeTest.wheel30FirstStopNeOneSet_nonempty_of_odd_nonsquare hn hns
  rw [PrimeTest.firstStopNeOne_wheel30_eq_classical hn.pos hn hns hclass hwheel]
  simpa only [PrimeTest.selfridgeD_natAbs] using
    classicalFirstStopNeOne_cast_le_log_sq_of_13_le hGRH hn13 hn hns

/-- Extend the logarithmic `g_ne1` bound to the full positive odd nonsquare range. -/
theorem classicalSelfridgeD_firstStopNeOne_natAbs_cast_le_max_thirteen_log_sq
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hnpos : 0 < n)
    (hn : Odd n) (hns : ¬IsSquare n) :
    ((PrimeTest.selfridgeD
            (PrimeTest.firstStopNeOne PrimeTest.isClassicalCandidate n
              (PrimeTest.classicalFirstStopNeOneSet_nonempty_of_odd_nonsquare hn hns))).natAbs :
        ℝ) ≤
      max 13 (Real.log (n : ℝ) ^ 2) := by
  by_cases hn13 : 13 ≤ n
  · exact
      (classicalSelfridgeD_firstStopNeOne_natAbs_cast_le_log_sq_of_13_le hGRH hn13 hn hns).trans
        (le_max_right _ _)
  · have hsmall :
      PrimeTest.firstStopNeOne PrimeTest.isClassicalCandidate n
          (PrimeTest.classicalFirstStopNeOneSet_nonempty_of_odd_nonsquare hn hns) ≤
        13 := by
      interval_cases n
      all_goals try (obtain ⟨k, hk⟩ := hn; omega)
      case «1» => exact (hns ⟨1, by norm_num only⟩).elim
      case «3» =>
        exact
          (PrimeTest.firstStopNeOne_le_candidate (i := 5) hn hns
            (by exact ⟨by norm_num only, by decide⟩)
                (by norm_num only)
                (by
                  rw [PrimeTest.jacobi_selfridgeD (by decide) hn]
                  norm_num only [PseudoSquare.jacobiSym_nat_mod_left'])).trans
            (by norm_num only)
      case «5» =>
        exact
          (PrimeTest.firstStopNeOne_le_candidate (i := 7) hn hns
            (by exact ⟨by norm_num only, by decide⟩)
                (by norm_num only)
                (by
                  rw [PrimeTest.jacobi_selfridgeD (by decide) hn]
                  norm_num only [PseudoSquare.jacobiSym_nat_mod_left'])).trans
            (by norm_num only)
      case «7» =>
        exact
          (PrimeTest.firstStopNeOne_le_candidate (i := 5) hn hns
            (by exact ⟨by norm_num only, by decide⟩)
                (by norm_num only)
                (by
                  rw [PrimeTest.jacobi_selfridgeD (by decide) hn]
                  norm_num only [PseudoSquare.jacobiSym_nat_mod_left'])).trans
            (by norm_num only)
      case «9» => exact (hns ⟨3, by norm_num only⟩).elim
      case «11» =>
        exact
          (PrimeTest.firstStopNeOne_le_candidate (i := 13) hn hns
            (by exact ⟨by norm_num only, by decide⟩)
                (by norm_num only)
                (by
                  rw [PrimeTest.jacobi_selfridgeD (by decide) hn]
                  norm_num only [PseudoSquare.jacobiSym_nat_mod_left'])).trans
            (by norm_num only)
    have hstopR :
      (PrimeTest.firstStopNeOne PrimeTest.isClassicalCandidate n
            (PrimeTest.classicalFirstStopNeOneSet_nonempty_of_odd_nonsquare hn hns) :
          ℝ) ≤
        13 :=
      Nat.cast_le.mpr hsmall
    have hsmallR :
      ((PrimeTest.selfridgeD
              (PrimeTest.firstStopNeOne PrimeTest.isClassicalCandidate n
                (PrimeTest.classicalFirstStopNeOneSet_nonempty_of_odd_nonsquare hn hns))).natAbs :
          ℝ) ≤
        13 := by
      simpa only [PrimeTest.selfridgeD_natAbs] using hstopR
    exact hsmallR.trans (le_max_left _ _)

theorem classicalSelfridgeD_firstStopNeOne_natAbs_cast_le_max_thirteen_log_sq_of_grh
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hnpos : 0 < n)
    (hn : Odd n) (hns : ¬IsSquare n) :
    ((PrimeTest.selfridgeD
            (PrimeTest.firstStopNeOne PrimeTest.isClassicalCandidate n
              (PrimeTest.classicalFirstStopNeOneSet_nonempty_of_odd_nonsquare hn hns))).natAbs :
        ℝ) ≤
      max 13 (Real.log (n : ℝ) ^ 2) := by
  exact classicalSelfridgeD_firstStopNeOne_natAbs_cast_le_max_thirteen_log_sq hGRH hnpos hn hns

/--
Under GRH, for an odd nonsquare `n ≥ 3`, the absolute classical pure `-1` stopping value is
at most `(log(4n) + (24/5)*loglog(4n) + 3)²`.
The proof bounds the stop by `max 27 (primeNegOneWitness n)`, bounds the witness by `QNegOne n`
and then by `elementaryRadius n`, and uses `31 < elementaryRadius n` to absorb `27`.
Rewriting `selfridgeD_natAbs` gives the absolute-value form used by the elementary-radius wrapper.
-/
theorem classicalSelfridgeD_firstStopNegOne_natAbs_cast_le_log_sq_of_3_le
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn3 : 3 ≤ n)
    (hn : Odd n) (hns : ¬IsSquare n) :
    ((PrimeTest.selfridgeD
            (PrimeTest.firstStopNegOne PrimeTest.isClassicalCandidate n
              (PrimeTest.classicalFirstStopNegOneSet_nonempty_of_odd_nonsquare hn hns))).natAbs :
        ℝ) ≤
      (Real.log (4 * (n : ℝ)) + (24 / 5 : ℝ) * Real.log (Real.log (4 * (n : ℝ))) + 3) ^ 2 := by
  let hw := PrimeTest.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns
  let hs := PrimeTest.classicalFirstStopNegOneSet_nonempty_of_odd_nonsquare hn hns
  have hstop := PrimeTest.classicalFirstStopNegOne_le_max_twenty_seven_primeWitness hn hw hs
  have hmem : n ∈ NumberTheory.admissibleFinset n := by
    apply NumberTheory.mem_admissibleFinset_iff.mpr
    exact ⟨by omega, le_rfl, hn, hns⟩
  have hq := PseudoSquare.primeNegOneWitness_le_QNegOne (B := n) (n := n) hmem
  have hQ := (PseudoSquare.elementary_formula_real hGRH hn3).2
  have hqR : (PrimeTest.primeNegOneWitness n hw : ℝ) ≤ PseudoSquare.elementaryRadius n := by
    exact (Nat.cast_le.mpr hq).trans hQ
  have h27 : (27 : ℝ) ≤ PseudoSquare.elementaryRadius n := by
    have h31 := PseudoSquare.thirtyOne_lt_elementaryRadius hn3
    linarith only [h31]
  have hstopR :
    (PrimeTest.firstStopNegOne PrimeTest.isClassicalCandidate n hs : ℝ) ≤
      PseudoSquare.elementaryRadius n := by
    have hstopCast :
      (PrimeTest.firstStopNegOne PrimeTest.isClassicalCandidate n hs : ℝ) ≤
        (max 27 (PrimeTest.primeNegOneWitness n hw) : ℝ) := by
      exact_mod_cast hstop
    exact hstopCast.trans (max_le h27 hqR)
  simpa only [PrimeTest.selfridgeD_natAbs, PseudoSquare.elementaryRadius] using hstopR

end PseudoPrime.PrimeTestBounds.Selfridge
