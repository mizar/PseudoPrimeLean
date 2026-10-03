/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

import PseudoPrime.PrimeTest.Selfridge.WitnessBridge
import PseudoPrime.PseudoSquare.Computation.QNeOneFiniteLogSq
import PseudoPrime.PseudoSquare.Computation.ResidueWheel
import PseudoPrime.PrimeTest.Selfridge.Nonempty
import PseudoPrime.PrimeTest.Selfridge.WitnessBounds

/-!
# Unconditional finite Selfridge logarithmic estimates
-/

namespace PseudoPrime.PrimeTestBounds.Selfridge

/-- A numerical logarithmic estimate used in the GRH assembly; no GRH is needed here. -/
theorem fifteen_lt_log_sq_of_forty_nine_le {n : ℕ} (hn : 49 ≤ n) :
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
  have hcast : (25 : ℝ) ≤ n := by
    exact_mod_cast (show 25 ≤ n by exact Nat.le_trans (by norm_num only : 25 ≤ 29) hn)
  have hmono :=
    Real.strictMonoOn_log.monotoneOn (by norm_num only : (0 : ℝ) < 25)
      (lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 25) hcast) hcast
  nlinarith only [hlog25, hmono, sq_nonneg (Real.log (n : ℝ) - 3)]

theorem classicalFirstStopNeOne_cast_le_log_sq_of_13_le_of_lt_49 {n : ℕ} (_hn13 : 13 ≤ n)
    (hn49 : n < 49) (hn : Odd n) (hns : ¬IsSquare n) :
    (PrimeTest.firstStopNeOne PrimeTest.isClassicalCandidate n
          (PrimeTest.classicalFirstStopNeOneSet_nonempty_of_odd_nonsquare hn hns) :
        ℝ) ≤
      Real.log (n : ℝ) ^ 2 := by
  interval_cases n
  all_goals (have hnmod := Nat.odd_iff.mp hn; norm_num only at hnmod)
  all_goals clear hnmod
  case «13» | «15» | «17» | «23» | «27» | «33» | «35» | «37» | «43» | «45» |
    «47» =>
    have hle :=
      PrimeTest.firstStopNeOne_le_candidate (i := 5) hn hns (by exact ⟨by norm_num only, by decide⟩)
        (by norm_num only)
        (by
          rw [PrimeTest.jacobi_selfridgeD (by decide) hn]
          norm_num only [PseudoSquare.jacobiSym_nat_mod_left'])
    exact (Nat.cast_le.mpr hle).trans (PseudoSquare.five_le_log_sq_of_eleven_le (by norm_num only))
  case «19» | «21» | «31» |
    «41» =>
    have hle :=
      PrimeTest.firstStopNeOne_le_candidate (i := 7) hn hns (by exact ⟨by norm_num only, by decide⟩)
        (by norm_num only)
        (by
          rw [PrimeTest.jacobi_selfridgeD (by decide) hn]
          norm_num only [PseudoSquare.jacobiSym_nat_mod_left'])
    exact
      (Nat.cast_le.mpr hle).trans (PseudoSquare.seven_le_log_sq_of_sixteen_le (by norm_num only))
  case
    «29» =>
    have hle :=
      PrimeTest.firstStopNeOne_le_candidate (i := 11) hn hns
        (by exact ⟨by norm_num only, by decide⟩) (by norm_num only)
        (by
          rw [PrimeTest.jacobi_selfridgeD (by decide) hn]
          norm_num only [PseudoSquare.jacobiSym_nat_mod_left'])
    exact (Nat.cast_le.mpr hle).trans (eleven_le_log_sq_of_twenty_nine_le (by norm_num only))
  case
    «39» =>
    have hle :=
      PrimeTest.firstStopNeOne_le_candidate (i := 9) hn hns (by exact ⟨by norm_num only, by decide⟩)
        (by norm_num only)
        (by
          rw [PrimeTest.jacobi_selfridgeD (by decide) hn]
          norm_num only [PseudoSquare.jacobiSym_nat_mod_left'])
    exact (Nat.cast_le.mpr hle).trans (nine_le_log_sq_of_twenty_nine_le (by norm_num only))
  case «25» => exact (hns ⟨5, by norm_num only⟩).elim

theorem classicalFirstStopNeOne_le_fifteen_of_13_le_of_lt_49 {n : ℕ} (_hn13 : 13 ≤ n)
    (hn49 : n < 49) (hn : Odd n) (hns : ¬IsSquare n) :
    PrimeTest.firstStopNeOne PrimeTest.isClassicalCandidate n
        (PrimeTest.classicalFirstStopNeOneSet_nonempty_of_odd_nonsquare hn hns) ≤
      15 := by
  let hw :=
    NumberTheory.primeNeOneWitnessSet_nonempty_of_negOne
      (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns)
  let hs := PrimeTest.classicalFirstStopNeOneSet_nonempty_of_odd_nonsquare hn hns
  have hmax :=
    PrimeTest.primeNeOneWitness_le_classicalFirstStop_le_max_unconditional hn.pos hn hns hw hs
  have hw7 :=
    PseudoSquare.primeNeOneWitness_le_seven_of_lt_sixtyFour hn hns
      (hn49.trans (by norm_num only : 49 < 64))
  have hw15 : NumberTheory.primeNeOneWitness n hw ≤ 15 := hw7.trans (by norm_num only)
  have hbound : max 15 (NumberTheory.primeNeOneWitness n hw) ≤ 15 := by exact (max_eq_left hw15).le
  exact hmax.2.trans hbound

end PseudoPrime.PrimeTestBounds.Selfridge
