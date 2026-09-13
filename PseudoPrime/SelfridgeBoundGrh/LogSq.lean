/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.PseudoSquare.Bounds.QNeOneLogSq
import PseudoPrime.PseudoSquare.Bounds.ElementaryOmegaFinal
import PseudoPrime.PseudoSquare.Bounds.WitnessMaximum
import PseudoPrime.PseudoSquare.Computation.QNeOneFiniteLogSq
import PseudoPrime.PseudoSquare.Computation.ResidueWheel
import PseudoPrime.AnalyticNumberTheory.GRH.Definition
import PseudoPrime.PrimeTest.Selfridge.Coincidence
import PseudoPrime.PrimeTest.Selfridge.Nonempty
import PseudoPrime.PrimeTest.Selfridge.WitnessBounds

/-!
# Pointwise logarithmic bounds for Selfridge stopping values

The analytic branch transfers the Q-side logarithmic witness bound through the
PrimeTest stopping comparison.  The finite branch below `49` remains separate.
-/

namespace PseudoPrime.SelfridgeBoundGrh

private theorem fifteen_lt_log_sq_of_forty_nine_le {n : ℕ} (hn : 49 ≤ n) :
    (15 : ℝ) < Real.log (n : ℝ) ^ 2 := by
  have h49 : (388 / 100 : ℝ) < Real.log 49 := by
    have h36 : (2 * (0.6931471803 + 1.0986122885 : ℝ)) < Real.log 36 := by
      rw [show (36 : ℝ) = 4 * 9 by norm_num only,
        Real.log_mul (by norm_num only) (by norm_num only), show (4 : ℝ) = 2 * 2 by norm_num only,
        show (9 : ℝ) = 3 * 3 by norm_num only]
      simp only [Real.log_mul (by norm_num only : (2 : ℝ) ≠ 0) (by norm_num only : (2 : ℝ) ≠ 0),
        Real.log_mul (by norm_num only : (3 : ℝ) ≠ 0) (by norm_num only : (3 : ℝ) ≠ 0)]
      nlinarith only [Real.log_two_gt_d9, Real.log_three_gt_d9]
    have hratio : (26 / 85 : ℝ) < Real.log ((49 : ℝ) / 36) := by
      have h := Real.lt_log_one_add_of_pos (x := (13 / 36 : ℝ)) (by norm_num only)
      convert h using 1 <;> norm_num only
    rw [show (49 : ℝ) = 36 * (49 / 36 : ℝ) by norm_num only,
      Real.log_mul (by norm_num only) (by norm_num only)]
    nlinarith only [h36, hratio]
  have hcast : (49 : ℝ) ≤ n := by exact_mod_cast hn
  have hmono :=
    Real.strictMonoOn_log.monotoneOn (by norm_num only : (0 : ℝ) < 49)
      (lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 49) hcast) hcast
  nlinarith only [h49, hmono, sq_nonneg (Real.log (n : ℝ) - (388 / 100 : ℝ))]

private theorem eleven_le_log_sq_of_twenty_nine_le {n : ℕ} (hn : 29 ≤ n) :
    (11 : ℝ) ≤ Real.log (n : ℝ) ^ 2 := by
  have hlog25 : (2 * (1.6094379123 : ℝ)) < Real.log 25 := by
    rw [show (25 : ℝ) = 5 * 5 by norm_num only, Real.log_mul (by norm_num only) (by norm_num only)]
    nlinarith only [Real.log_five_gt_d9]
  have hratio : (4 / 27 : ℝ) < Real.log ((29 : ℝ) / 25) := by
    have h := Real.lt_log_one_add_of_pos (x := (4 / 25 : ℝ)) (by norm_num only)
    convert h using 1 <;> norm_num only
  have hlog29 : (2 * (1.6094379123 : ℝ) + 4 / 27) < Real.log 29 := by
    rw [show (29 : ℝ) = 25 * (29 / 25 : ℝ) by norm_num only,
      Real.log_mul (by norm_num only) (by norm_num only)]
    nlinarith only [hlog25, hratio]
  have hcast : (29 : ℝ) ≤ n := by exact_mod_cast hn
  have hmono :=
    Real.strictMonoOn_log.monotoneOn (by norm_num only : (0 : ℝ) < 29)
      (lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 29) hcast) hcast
  nlinarith only [hlog29, hmono, sq_nonneg (Real.log (n : ℝ) - (33 / 10 : ℝ))]

private theorem nine_le_log_sq_of_twenty_nine_le {n : ℕ} (hn : 29 ≤ n) :
    (9 : ℝ) ≤ Real.log (n : ℝ) ^ 2 := by
  have hlog25 : (2 * (1.6094379123 : ℝ)) < Real.log 25 := by
    rw [show (25 : ℝ) = 5 * 5 by norm_num only, Real.log_mul (by norm_num only) (by norm_num only)]
    nlinarith only [Real.log_five_gt_d9]
  have hcast : (25 : ℝ) ≤ n := by exact_mod_cast (show 25 ≤ n by omega)
  have hmono :=
    Real.strictMonoOn_log.monotoneOn (by norm_num only : (0 : ℝ) < 25)
      (lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 25) hcast) hcast
  nlinarith only [hlog25, hmono, sq_nonneg (Real.log (n : ℝ) - 3)]

private theorem firstStopNeOne_le_candidate {n i : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hi : PrimeTest.isClassicalCandidate i) (hndvd : ¬n ∣ i)
    (hvalue : jacobiSym (PrimeTest.selfridgeD i) n ≠ 1) :
    PrimeTest.firstStopNeOne PrimeTest.isClassicalCandidate n
        (PrimeTest.classicalFirstStopNeOneSet_nonempty_of_odd_nonsquare hn hns) ≤
      i := by
  apply
    PrimeTest.firstStopNeOne_le PrimeTest.isClassicalCandidate n
      (PrimeTest.classicalFirstStopNeOneSet_nonempty_of_odd_nonsquare hn hns)
  exact ⟨hi, hndvd, hvalue⟩

theorem classicalFirstStopNeOne_cast_le_log_sq_of_13_le_of_lt_49 {n : ℕ} (hn13 : 13 ≤ n)
    (hn49 : n < 49) (hn : Odd n) (hns : ¬IsSquare n) :
    (PrimeTest.firstStopNeOne PrimeTest.isClassicalCandidate n
          (PrimeTest.classicalFirstStopNeOneSet_nonempty_of_odd_nonsquare hn hns) :
        ℝ) ≤
      Real.log (n : ℝ) ^ 2 := by
  interval_cases n
  all_goals try (obtain ⟨k, hk⟩ := hn; omega)
  case «13» | «15» | «17» | «23» | «27» | «33» | «35» | «37» | «43» | «45» |
    «47» =>
    have hle :=
      firstStopNeOne_le_candidate (i := 5) hn hns (by exact ⟨by norm_num only, by decide⟩)
        (by norm_num only)
        (by
          rw [PrimeTest.jacobi_selfridgeD (by decide) hn]
          norm_num only [PseudoSquare.jacobiSym_nat_mod_left'])
    exact
      (Nat.cast_le.mpr hle).trans (PseudoSquare.five_le_log_sq_of_eleven_le (by omega))
  case «19» | «21» | «31» |
    «41» =>
    have hle :=
      firstStopNeOne_le_candidate (i := 7) hn hns (by exact ⟨by norm_num only, by decide⟩)
        (by norm_num only)
        (by
          rw [PrimeTest.jacobi_selfridgeD (by decide) hn]
          norm_num only [PseudoSquare.jacobiSym_nat_mod_left'])
    exact
      (Nat.cast_le.mpr hle).trans
        (PseudoSquare.seven_le_log_sq_of_sixteen_le (by omega))
  case
    «29» =>
    have hle :=
      firstStopNeOne_le_candidate (i := 11) hn hns (by exact ⟨by norm_num only, by decide⟩)
        (by norm_num only)
        (by
          rw [PrimeTest.jacobi_selfridgeD (by decide) hn]
          norm_num only [PseudoSquare.jacobiSym_nat_mod_left'])
    exact (Nat.cast_le.mpr hle).trans (eleven_le_log_sq_of_twenty_nine_le (by omega))
  case
    «39» =>
    have hle :=
      firstStopNeOne_le_candidate (i := 9) hn hns (by exact ⟨by norm_num only, by decide⟩)
        (by norm_num only)
        (by
          rw [PrimeTest.jacobi_selfridgeD (by decide) hn]
          norm_num only [PseudoSquare.jacobiSym_nat_mod_left'])
    exact (Nat.cast_le.mpr hle).trans (nine_le_log_sq_of_twenty_nine_le (by omega))
  case «25» => exact (hns ⟨5, by norm_num only⟩).elim

theorem classicalFirstStopNeOne_cast_le_log_sq_of_49_le
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ}
    (hn49 : 49 ≤ n) (hn : Odd n) (hns : ¬IsSquare n) :
    (PrimeTest.firstStopNeOne PrimeTest.isClassicalCandidate n
          (PrimeTest.classicalFirstStopNeOneSet_nonempty_of_odd_nonsquare hn hns) :
        ℝ) ≤
      Real.log (n : ℝ) ^ 2 := by
  let hs := PrimeTest.classicalFirstStopNeOneSet_nonempty_of_odd_nonsquare hn hns
  obtain ⟨hw, hqR⟩ :=
    PseudoSquare.exists_primeNeOneWitness_cast_le_log_sq_of_odd_nonsquare hGRH hn hns
      (by omega)
  have hmax :=
    PrimeTest.primeNeOneWitness_le_classicalFirstStop_le_max_unconditional hn.pos hn hns
      hw hs
  have hmaxR :
    (PrimeTest.firstStopNeOne PrimeTest.isClassicalCandidate n hs : ℝ) ≤
      ((max 15 (NumberTheory.primeNeOneWitness n hw) : ℕ) : ℝ) := by
    exact_mod_cast hmax.2
  have hlog : (15 : ℝ) ≤ Real.log (n : ℝ) ^ 2 := (fifteen_lt_log_sq_of_forty_nine_le hn49).le
  have hmaxlog :
    ((max 15 (NumberTheory.primeNeOneWitness n hw) : ℕ) : ℝ) ≤
      Real.log (n : ℝ) ^ 2 := by
    simpa using (max_le hlog hqR)
  exact hmaxR.trans hmaxlog

theorem classicalSelfridgeD_firstStopNeOne_natAbs_cast_le_log_sq_of_49_le
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ}
    (hn49 : 49 ≤ n) (hn : Odd n) (hns : ¬IsSquare n) :
    ((PrimeTest.selfridgeD
            (PrimeTest.firstStopNeOne PrimeTest.isClassicalCandidate n
              (PrimeTest.classicalFirstStopNeOneSet_nonempty_of_odd_nonsquare hn
                hns))).natAbs :
        ℝ) ≤
      Real.log (n : ℝ) ^ 2 := by
  simpa only [PrimeTest.selfridgeD_natAbs] using
    classicalFirstStopNeOne_cast_le_log_sq_of_49_le hGRH hn49 hn hns

theorem classicalFirstStopNeOne_le_fifteen_of_13_le_of_lt_49 {n : ℕ} (hn13 : 13 ≤ n) (hn49 : n < 49)
    (hn : Odd n) (hns : ¬IsSquare n) :
    PrimeTest.firstStopNeOne PrimeTest.isClassicalCandidate n
        (PrimeTest.classicalFirstStopNeOneSet_nonempty_of_odd_nonsquare hn hns) ≤
      15 := by
  let hw :=
    NumberTheory.primeNeOneWitnessSet_nonempty_of_negOne
      (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns)
  let hs := PrimeTest.classicalFirstStopNeOneSet_nonempty_of_odd_nonsquare hn hns
  have hmax :=
    PrimeTest.primeNeOneWitness_le_classicalFirstStop_le_max_unconditional hn.pos hn hns
      hw hs
  have hw7 :=
    PseudoSquare.primeNeOneWitness_le_seven_of_lt_sixtyFour hn hns (by omega : n < 64)
  have hw15 : NumberTheory.primeNeOneWitness n hw ≤ 15 := hw7.trans (by norm_num)
  have hbound : max 15 (NumberTheory.primeNeOneWitness n hw) ≤ 15 := by
    exact (max_eq_left hw15).le
  exact hmax.2.trans hbound

theorem classicalFirstStopNeOne_cast_le_log_sq_of_13_le
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ}
    (hn13 : 13 ≤ n) (hn : Odd n) (hns : ¬IsSquare n) :
    (PrimeTest.firstStopNeOne PrimeTest.isClassicalCandidate n
          (PrimeTest.classicalFirstStopNeOneSet_nonempty_of_odd_nonsquare hn hns) :
        ℝ) ≤
      Real.log (n : ℝ) ^ 2 := by
  by_cases hn49 : n < 49
  · exact classicalFirstStopNeOne_cast_le_log_sq_of_13_le_of_lt_49 hn13 hn49 hn hns
  · exact classicalFirstStopNeOne_cast_le_log_sq_of_49_le hGRH (by omega) hn hns

theorem classicalSelfridgeD_firstStopNeOne_natAbs_cast_le_log_sq_of_13_le
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ}
    (hn13 : 13 ≤ n) (hn : Odd n) (hns : ¬IsSquare n) :
    ((PrimeTest.selfridgeD
            (PrimeTest.firstStopNeOne PrimeTest.isClassicalCandidate n
              (PrimeTest.classicalFirstStopNeOneSet_nonempty_of_odd_nonsquare hn
                hns))).natAbs :
        ℝ) ≤
      Real.log (n : ℝ) ^ 2 := by
  simpa only [PrimeTest.selfridgeD_natAbs] using
    classicalFirstStopNeOne_cast_le_log_sq_of_13_le hGRH hn13 hn hns

theorem wheel30SelfridgeD_firstStopNeOne_natAbs_cast_le_log_sq_of_13_le
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ}
    (hn13 : 13 ≤ n) (hn : Odd n) (hns : ¬IsSquare n) :
    ((PrimeTest.selfridgeD
            (PrimeTest.firstStopNeOne PrimeTest.isWheel30NeOneCandidate n
              (PrimeTest.wheel30FirstStopNeOneSet_nonempty_of_odd_nonsquare hn
                hns))).natAbs :
        ℝ) ≤
      Real.log (n : ℝ) ^ 2 := by
  let hclass := PrimeTest.classicalFirstStopNeOneSet_nonempty_of_odd_nonsquare hn hns
  let hwheel := PrimeTest.wheel30FirstStopNeOneSet_nonempty_of_odd_nonsquare hn hns
  rw [PrimeTest.firstStopNeOne_wheel30_eq_classical hn.pos hn hns hclass hwheel]
  simpa only [PrimeTest.selfridgeD_natAbs] using
    classicalFirstStopNeOne_cast_le_log_sq_of_13_le hGRH hn13 hn hns

/-- Extend the logarithmic `g_ne1` bound to the full positive odd nonsquare range. -/
theorem classicalSelfridgeD_firstStopNeOne_natAbs_cast_le_max_thirteen_log_sq
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ}
    (hnpos : 0 < n) (hn : Odd n) (hns : ¬IsSquare n) :
    ((PrimeTest.selfridgeD
            (PrimeTest.firstStopNeOne PrimeTest.isClassicalCandidate n
              (PrimeTest.classicalFirstStopNeOneSet_nonempty_of_odd_nonsquare hn
                hns))).natAbs :
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
          (firstStopNeOne_le_candidate (i := 5) hn hns (by exact ⟨by norm_num only, by decide⟩)
                (by norm_num only)
                (by
                  rw [PrimeTest.jacobi_selfridgeD (by decide) hn]
                  norm_num only [PseudoSquare.jacobiSym_nat_mod_left'])).trans
            (by norm_num only)
      case «5» =>
        exact
          (firstStopNeOne_le_candidate (i := 7) hn hns (by exact ⟨by norm_num only, by decide⟩)
                (by norm_num only)
                (by
                  rw [PrimeTest.jacobi_selfridgeD (by decide) hn]
                  norm_num only [PseudoSquare.jacobiSym_nat_mod_left'])).trans
            (by norm_num only)
      case «7» =>
        exact
          (firstStopNeOne_le_candidate (i := 5) hn hns (by exact ⟨by norm_num only, by decide⟩)
                (by norm_num only)
                (by
                  rw [PrimeTest.jacobi_selfridgeD (by decide) hn]
                  norm_num only [PseudoSquare.jacobiSym_nat_mod_left'])).trans
            (by norm_num only)
      case «9» => exact (hns ⟨3, by norm_num only⟩).elim
      case «11» =>
        exact
          (firstStopNeOne_le_candidate (i := 13) hn hns (by exact ⟨by norm_num only, by decide⟩)
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
                (PrimeTest.classicalFirstStopNeOneSet_nonempty_of_odd_nonsquare hn
                  hns))).natAbs :
          ℝ) ≤
        13 := by
      simpa only [PrimeTest.selfridgeD_natAbs] using hstopR
    exact hsmallR.trans (le_max_left _ _)

theorem classicalSelfridgeD_firstStopNeOne_natAbs_cast_le_max_thirteen_log_sq_of_grh
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ}
    (hnpos : 0 < n) (hn : Odd n) (hns : ¬IsSquare n) :
    ((PrimeTest.selfridgeD
            (PrimeTest.firstStopNeOne PrimeTest.isClassicalCandidate n
              (PrimeTest.classicalFirstStopNeOneSet_nonempty_of_odd_nonsquare hn
                hns))).natAbs :
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
              (PrimeTest.classicalFirstStopNegOneSet_nonempty_of_odd_nonsquare hn
                hns))).natAbs :
        ℝ) ≤
      (Real.log (4 * (n : ℝ)) + (24 / 5 : ℝ) * Real.log (Real.log (4 * (n : ℝ))) + 3) ^ 2 := by
  let hw := PrimeTest.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns
  let hs := PrimeTest.classicalFirstStopNegOneSet_nonempty_of_odd_nonsquare hn hns
  have hstop :=
    PrimeTest.classicalFirstStopNegOne_le_max_twenty_seven_primeWitness hn hw hs
  have hmem : n ∈ NumberTheory.admissibleFinset n := by
    apply NumberTheory.mem_admissibleFinset_iff.mpr
    exact ⟨by omega, le_rfl, hn, hns⟩
  have hq := PseudoSquare.primeNegOneWitness_le_QNegOne (B := n) (n := n) hmem
  have hQ := (PseudoSquare.elementary_formula_real hGRH hn3).2
  have hqR :
    (PrimeTest.primeNegOneWitness n hw : ℝ) ≤
      PseudoSquare.elementaryRadius n := by
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
  simpa only [PrimeTest.selfridgeD_natAbs,
    PseudoSquare.elementaryRadius] using hstopR

end PseudoPrime.SelfridgeBoundGrh
