/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.NextWitnessEnvelope

/-! # Strict continuous improvements of the next witness envelope -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- On the stated continuous range, the next envelope strictly improves its base. -/
theorem next_lt_low_range {n : ℕ} (hN : 3000 ≤ n) (hU : Real.log n ≤ 553 / 50) :
    nextWitnessEnvelope n < improvedWitnessEnvelope n := by
  exact (nextWitnessEnvelope_le_low n).trans_lt (lowPrimeEnvelope_lt_improved hN hU)

/-- On the stated continuous range, the next envelope strictly improves its base. -/
theorem next_lt_gaussian1000 {n : ℕ} (hn : 1 < n) (hL : 132 ≤ Real.log n) (hU : Real.log n ≤ 235) :
    nextWitnessEnvelope n < improvedWitnessEnvelope n := by
  rw [improved_eq_selected hn]
  exact (next_le_gaussian1000 (by linarith only [hL])).trans_lt (gaussian1000_lt_improved hn hL hU)

/-- On the stated continuous range, the next envelope strictly improves its base. -/
theorem next_lt_reflected {n : ℕ} (hn : 1 < n) (hL : 109 ≤ Real.log n)
    (hU : Real.log n < gammaReflectedFixedSwitch) :
    nextWitnessEnvelope n < improvedWitnessEnvelope n := by
  rw [improved_eq_selected hn]
  exact (next_le_reflected (by linarith only [hL])).trans_lt (gammaReflected_lt_improved hn hL hU)

/-- On the stated continuous range, the next envelope strictly improves its base. -/
theorem next_lt_fixed61 {n : ℕ} (hn : 1 < n) (hL : 2877 / 250 < Real.log n)
    (hU : Real.log n ≤ 11509 / 1000) : nextWitnessEnvelope n < improvedWitnessEnvelope n := by
  rw [improved_eq_fixed67 hn hL (by linarith only [hU])]
  exact (next_le_fixed61 hU).trans_lt (by norm_num only)

/-- On the stated continuous range, the next envelope strictly improves its base. -/
theorem next_lt_fixed67 {n : ℕ} (hn : 1 < n) (hL : 47 / 4 < Real.log n)
    (hU : Real.log n ≤ 1179 / 100) : nextWitnessEnvelope n < improvedWitnessEnvelope n := by
  rw [improved_eq_fourStep hn hL (by linarith only [hU])]
  exact (next_le_fixed67 hU).trans_lt (LLS.PaperStatements.fourStep_step_gt67 hL.le)

/-- On the stated continuous range, the next envelope strictly improves its base. -/
theorem next_lt_fixed71 {n : ℕ} (hn : 1 < n) (hL : 1179 / 100 < Real.log n)
    (hU : Real.log n ≤ 1193 / 100) : nextWitnessEnvelope n < improvedWitnessEnvelope n := by
  rw [improved_eq_fourStep hn (by linarith only [hL]) (by linarith only [hU])]
  exact (next_le_fixed71 hU).trans_lt (LLS.PaperStatements.fourStep_step_gt71 hL.le)

/-- On the stated continuous range, the next envelope strictly improves its base. -/
theorem next_lt_fixed73 {n : ℕ} (hn : 1 < n) (hL : 1193 / 100 < Real.log n)
    (hU : Real.log n ≤ 12337 / 1000) : nextWitnessEnvelope n < improvedWitnessEnvelope n := by
  rw [improved_eq_fourStep hn (by linarith only [hL]) (by linarith only [hU])]
  exact (next_le_fixed73 hU).trans_lt (LLS.PaperStatements.fourStep_step_gt73 hL.le)

/-- On the stated continuous range, the next envelope strictly improves its base. -/
theorem next_lt_pointwise {n : ℕ} (hn : 1 < n) (hL : 47 / 4 < Real.log n) (hU : Real.log n < 100) :
    nextWitnessEnvelope n < improvedWitnessEnvelope n := by
  rw [improved_eq_fourStep hn hL hU]
  exact
    (next_le_pointwise).trans_lt
      (LLS.PaperStatements.pointwiseCutoff_lt_fourStep (by linarith only [hL]))

/-- On the stated continuous range, the next envelope strictly improves its base. -/
theorem next_lt_seeded {n : ℕ} (hn : 1 < n) (hU : Real.log n < 2000000000000)
    (hs :
      (Analysis.gaussianFloorSwitch false 35000 < Real.log n ∧
          Real.log n < Analysis.gaussianSeededSwitch false 50000) ∨
        Analysis.gaussianFloorSwitch true 50000 < Real.log n) :
    nextWitnessEnvelope n < improvedWitnessEnvelope n := by
  have h63 : (63 : ℝ) ≤ Real.log n := by
    rcases hs with h | h
    · linarith only [h.1, Analysis.gaussianFloor_switch35_bounds.1]
    · linarith only [h, (Analysis.gaussianFloor_switch50_bounds true).1]
  exact (next_le_seeded h63).trans_lt (gaussianSeeded_lt_improved hn hU hs)

/-- On the stated continuous range, the next envelope strictly improves its base. -/
theorem next_lt_early {n : ℕ} (hn : 1 < n) (hL : 1500000000000 ≤ Real.log n)
    (hU : Real.log n < 2000000000000) : nextWitnessEnvelope n < improvedWitnessEnvelope n := by
  rw [improved_eq_gaussian hn (by linarith only [hL]) hU]
  have hs := Analysis.gaussianFloorSelected_lower (by linarith only [hL] : 63 ≤ Real.log n)
  have hp : 0 < Real.log n ^ 2 := sq_pos_of_pos (by linarith only [hL])
  have hc : (282924 / 1000000 : ℝ) * Real.log n ^ 2 < (15 / 32 : ℝ) * Real.log n ^ 2 :=
    mul_lt_mul_of_pos_right (by norm_num only) hp
  exact (next_le_early hL).trans_lt (hc.trans hs)

/-- On the stated continuous range, the next envelope strictly improves its base. -/
theorem next_lt_triangular {n : ℕ} (hn : 1 < n) (hL : 2000000000000 ≤ Real.log n) :
    nextWitnessEnvelope n < improvedWitnessEnvelope n := by
  rw [improved_eq_triangular hn hL]
  have hp : 0 < Real.log n ^ 2 := sq_pos_of_pos (by linarith only [hL])
  exact (next_le_triangular hL).trans_lt (mul_lt_mul_of_pos_right (by norm_num only) hp)

end PseudoPrime.PrimeTestBounds.MillerRabin
