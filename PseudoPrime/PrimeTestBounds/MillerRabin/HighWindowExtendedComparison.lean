/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.HighWindowExtended
public import PseudoPrime.PrimeTestBounds.MillerRabin.HighWindowComparison

/-! # Strict comparisons for later high-window candidates -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Before 250 billion, a lower bound of 3315/10000 for the base is preserved by every
active tuned profile. The remaining profiles have entrances beyond this interval. -/
theorem tunedHigh_lower_03315 {L B : ℝ} (hU : L < 250000000000)
    (hB : (3315 / 10000 : ℝ) * L ^ 2 ≤ B) : (3315 / 10000 : ℝ) * L ^ 2 ≤ tunedHighMin L B := by
  apply tunedHigh_lower hB
  intro i hi
  fin_cases i <;>
    first
    | (change (1480000000000 : ℝ) ≤ L at hi; linarith only [hi, hU])
    |
      (norm_num only [triangularTunedProfile, triangularP04603, triangularP04145, triangularP03315,
         triangularP02992, triangularP02891, triangularP028399] at hi ⊢;
       nlinarith only [hi, hU, sq_nonneg L])

/-- Before 500 billion, a lower bound of 2992/10000 for the base is preserved by every
active tuned profile. -/
theorem tunedHigh_lower_02992 {L B : ℝ} (hU : L < 500000000000)
    (hB : (2992 / 10000 : ℝ) * L ^ 2 ≤ B) : (2992 / 10000 : ℝ) * L ^ 2 ≤ tunedHighMin L B := by
  apply tunedHigh_lower hB
  intro i hi
  fin_cases i <;>
    first
    | (change (1480000000000 : ℝ) ≤ L at hi; linarith only [hi, hU])
    |
      (norm_num only [triangularTunedProfile, triangularP04603, triangularP04145, triangularP03315,
         triangularP02992, triangularP02891, triangularP028399] at hi ⊢;
       nlinarith only [hi, hU, sq_nonneg L])

/-- Before 1080 billion, a lower bound of 2891/10000 for the base is preserved by every
active tuned profile. -/
theorem tunedHigh_lower_02891 {L B : ℝ} (hU : L < 1080000000000)
    (hB : (2891 / 10000 : ℝ) * L ^ 2 ≤ B) : (2891 / 10000 : ℝ) * L ^ 2 ≤ tunedHighMin L B := by
  apply tunedHigh_lower hB
  intro i hi
  fin_cases i <;>
    first
    | (change (1480000000000 : ℝ) ≤ L at hi; linarith only [hi, hU])
    |
      (norm_num only [triangularTunedProfile, triangularP04603, triangularP04145, triangularP03315,
         triangularP02992, triangularP02891, triangularP028399] at hi ⊢;
       nlinarith only [hi, hU, sq_nonneg L])

/-- A common quadratic lower bound for the tuned high minimum extends to the full
previous selected cutoff on the later windows. The coefficient restriction also bounds
the retained Gaussian, four-ninths, seven-sixteenths and 173/500 candidates. -/
theorem highWindow_lower_of_tuned {n : ℕ} {C : ℝ} (hL : (80000000000 : ℝ) ≤ Real.log n)
    (hC : C ≤ 173 / 500)
    (hH : C * Real.log n ^ 2 ≤ tunedHighMin (Real.log n) (tunedFiniteSelected n)) :
    C * Real.log n ^ 2 ≤ highWindowSelected n := by
  have h63 : (63 : ℝ) ≤ Real.log n := by linarith only [hL]
  have h70 : (70000 : ℝ) ≤ Real.log n := by linarith only [hL]
  have h0 : (0 : ℝ) ≤ Real.log n := by linarith only [hL]
  have hN := large_of_log63 h63
  have hg := seededSurplusFamily_lower h63
  have ht := gaussianTight_bound_lower h0
  have hs := sq_nonneg (Real.log n)
  have hc := mul_le_mul_of_nonneg_right hC hs
  rw [highWindowSelected, ite_eq_right (not_lt.mpr hN), ite_eq_left hL, highCoeffSelected,
    ite_eq_right (not_lt.mpr hN), ite_eq_left h70, fourNinthsSelectedEnvelope,
    ite_eq_right (not_lt.mpr hN), nextTunedSelected_eq_normal, nextTunedNormalSelected,
    ite_eq_right (not_lt.mpr hN), ite_eq_left h63]
  refine le_min (le_min (le_min (le_min hH (le_min ?_ ?_)) ?_) ?_) ?_ <;>
    nlinarith only [hc, hs, hg, ht]

/-- On an original triangular stage, the finite tuned base equals the corresponding
sharp-stage coefficient. The finite guards have expired by the first high entrance. -/
theorem tunedFinite_eq_stage (i : Fin 7) {n : ℕ} (hn : 1 < n)
    (hL : (triangularProfile i.castSucc).T ≤ Real.log n)
    (hU : Real.log n < (triangularProfile i.succ).T) :
    tunedFiniteSelected n = (triangularProfile i.castSucc).C * Real.log n ^ 2 := by
  have hentry := (triangularProfile i.castSucc).entry.trans hL
  have hl : (126409 / 10000 : ℝ) < Real.log n := by linarith only [hentry]
  rw [← tunedFinite_eq_selected hn, tunedFinite_eq_sharp_of_log hn hl, sharp_eq_selected hn]
  exact sharpSelected_eq_triangularStage i hn hL hU

/-- From 120 billion to 300 billion, the extended cutoff is at most 323/1000 of the square. -/
theorem highWindowExtended_le_0323 {n : ℕ} (hL : (120000000000 : ℝ) ≤ Real.log n)
    (hU : Real.log n < 300000000000) :
    highWindowExtended n ≤ (323 / 1000 : ℝ) * Real.log n ^ 2 := by
  have h600 : ¬(600000000000 : ℝ) ≤ Real.log n :=
    not_le_of_gt (lt_of_lt_of_le hU (by norm_num only))
  rw [highWindowExtended, ite_eq_right h600, ite_eq_right (not_le_of_gt hU), ite_eq_left hL]
  exact min_le_right _ _

/-- From 300 billion to 600 billion, the extended cutoff is at most 37/125 of the square. -/
theorem highWindowExtended_le_0296 {n : ℕ} (hL : (300000000000 : ℝ) ≤ Real.log n)
    (hU : Real.log n < 600000000000) : highWindowExtended n ≤ (37 / 125 : ℝ) * Real.log n ^ 2 := by
  rw [highWindowExtended, ite_eq_right (not_le_of_gt hU), ite_eq_left hL]
  exact min_le_right _ _

/-- Above 600 billion, the extended cutoff is at most 36/125 of the squared logarithm. -/
theorem highWindowExtended_le_0288 {n : ℕ} (hL : (600000000000 : ℝ) ≤ Real.log n) :
    highWindowExtended n ≤ (36 / 125 : ℝ) * Real.log n ^ 2 := by
  rw [highWindowExtended, ite_eq_left hL]
  exact min_le_right _ _

/-- The 323/1000 profile strictly improves the complete earlier selected envelope until
the next original tuned entrance. -/
theorem highWindowExtended_lt_0323 {n : ℕ} (hL : (120000000000 : ℝ) ≤ Real.log n)
    (hU : Real.log n < 250000000000) : highWindowExtended n < highWindowSelected n := by
  have h80 : (80000000000 : ℝ) ≤ Real.log n := by linarith only [hL]
  have h63 : (63 : ℝ) ≤ Real.log n := by linarith only [hL]
  have hn : 1 < n := lt_of_lt_of_le (by norm_num only) (large_of_log63 h63)
  have hstart : (100000000000 : ℝ) ≤ Real.log n := by linarith only [hL]
  have hs : 0 < Real.log n ^ 2 := sq_pos_of_pos (by linarith only [hL])
  have heq := tunedFinite_eq_stage 2 hn hstart hU
  change tunedFiniteSelected n = (1 / 3 : ℝ) * Real.log n ^ 2 at heq
  have hB : (3315 / 10000 : ℝ) * Real.log n ^ 2 ≤ tunedFiniteSelected n := by
    rw [heq]
    nlinarith only [hs]
  have hold := highWindow_lower_of_tuned h80 (by norm_num only) (tunedHigh_lower_03315 hU hB)
  have hupper : Real.log n < 300000000000 := by linarith only [hU]
  have hnew := highWindowExtended_le_0323 hL hupper
  nlinarith only [hnew, hold, hs]

/-- The 37/125 profile strictly improves the complete earlier selected envelope until
the next original tuned entrance. -/
theorem highWindowExtended_lt_0296 {n : ℕ} (hL : (300000000000 : ℝ) ≤ Real.log n)
    (hU : Real.log n < 500000000000) : highWindowExtended n < highWindowSelected n := by
  have h80 : (80000000000 : ℝ) ≤ Real.log n := by linarith only [hL]
  have h63 : (63 : ℝ) ≤ Real.log n := by linarith only [hL]
  have hn : 1 < n := lt_of_lt_of_le (by norm_num only) (large_of_log63 h63)
  have hstart : (250000000000 : ℝ) ≤ Real.log n := by linarith only [hL]
  have hs : 0 < Real.log n ^ 2 := sq_pos_of_pos (by linarith only [hL])
  have heq := tunedFinite_eq_stage 3 hn hstart hU
  change tunedFiniteSelected n = (3 / 10 : ℝ) * Real.log n ^ 2 at heq
  have hB : (2992 / 10000 : ℝ) * Real.log n ^ 2 ≤ tunedFiniteSelected n := by
    rw [heq]
    nlinarith only [hs]
  have hold := highWindow_lower_of_tuned h80 (by norm_num only) (tunedHigh_lower_02992 hU hB)
  have hupper : Real.log n < 600000000000 := by linarith only [hU]
  have hnew := highWindowExtended_le_0296 hL hupper
  nlinarith only [hnew, hold, hs]

/-- The 36/125 profile strictly improves the complete earlier selected envelope until
the next original tuned entrance. -/
theorem highWindowExtended_lt_0288 {n : ℕ} (hL : (600000000000 : ℝ) ≤ Real.log n)
    (hU : Real.log n < 1080000000000) : highWindowExtended n < highWindowSelected n := by
  have h80 : (80000000000 : ℝ) ≤ Real.log n := by linarith only [hL]
  have h63 : (63 : ℝ) ≤ Real.log n := by linarith only [hL]
  have hn : 1 < n := lt_of_lt_of_le (by norm_num only) (large_of_log63 h63)
  have hstart : (500000000000 : ℝ) ≤ Real.log n := by linarith only [hL]
  have hs : 0 < Real.log n ^ 2 := sq_pos_of_pos (by linarith only [hL])
  have heq := tunedFinite_eq_stage 4 hn hstart hU
  change tunedFiniteSelected n = (29 / 100 : ℝ) * Real.log n ^ 2 at heq
  have hB : (2891 / 10000 : ℝ) * Real.log n ^ 2 ≤ tunedFiniteSelected n := by
    rw [heq]
    nlinarith only [hs]
  have hold := highWindow_lower_of_tuned h80 (by norm_num only) (tunedHigh_lower_02891 hU hB)
  have hnew := highWindowExtended_le_0288 hL
  nlinarith only [hnew, hold, hs]

end PseudoPrime.PrimeTestBounds.MillerRabin
