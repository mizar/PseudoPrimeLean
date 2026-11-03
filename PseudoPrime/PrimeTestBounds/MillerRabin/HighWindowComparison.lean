/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.HighWindowEnvelope
public import PseudoPrime.PrimeTestBounds.MillerRabin.NextTunedNormalForm
public import PseudoPrime.PrimeTestBounds.MillerRabin.TriangularTunedOrder

/-! # Comparisons for high-window witness cutoffs -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Below the second tuned-profile entrance, every active tuned profile has coefficient at
least `7/16`. A common lower bound for the base therefore transfers through the guarded minimum. -/
theorem tunedHigh_lower_7_16 {L B : ℝ} (hU : L < 40000000000) (hB : (7 / 16 : ℝ) * L ^ 2 ≤ B) :
    (7 / 16 : ℝ) * L ^ 2 ≤ tunedHighMin L B := by
  apply tunedHigh_lower hB
  intro i hi
  fin_cases i <;>
    first
    | (change (1480000000000 : ℝ) ≤ L at hi; linarith only [hi, hU])
    |
      (norm_num only [triangularTunedProfile, triangularP04603, triangularP04145, triangularP03315,
         triangularP02992, triangularP02891, triangularP028399] at hi ⊢;
       nlinarith only [hi, hU, sq_nonneg L])

/-- Before the second triangular entrance, the previous public cutoff is bounded below by
`7/16` of the squared logarithm whenever the finite base has that lower bound. -/
theorem highCoeff_lower_7_16_of_finite {n : ℕ} (hL : (70000 : ℝ) ≤ Real.log n)
    (hU : Real.log n < 40000000000) (hB : (7 / 16 : ℝ) * Real.log n ^ 2 ≤ tunedFiniteSelected n) :
    (7 / 16 : ℝ) * Real.log n ^ 2 ≤ highCoeffSelected n := by
  have h63 : (63 : ℝ) ≤ Real.log n := by linarith only [hL]
  have h0 : (0 : ℝ) ≤ Real.log n := by linarith only [hL]
  have hN := large_of_log63 h63
  have hg := seededSurplusFamily_lower h63
  have ht := gaussianTight_bound_lower h0
  have hs := sq_nonneg (Real.log n)
  rw [highCoeffSelected, ite_eq_right (not_lt.mpr hN), ite_eq_left hL, fourNinthsSelectedEnvelope,
    ite_eq_right (not_lt.mpr hN), nextTunedSelected_eq_normal, nextTunedNormalSelected,
    ite_eq_right (not_lt.mpr hN), ite_eq_left h63]
  refine le_min (le_min (le_min (tunedHigh_lower_7_16 hU hB) (le_min ?_ ?_)) ?_) ?_ <;>
    nlinarith only [hg, ht, hs]

/-- Between the first two original triangular entrances, the finite selected base has
coefficient `7/15`; the endpoint guards have already expired. -/
theorem tunedFinite_eq_early_window {n : ℕ} (hL : (30000000000 : ℝ) ≤ Real.log n)
    (hU : Real.log n < 40000000000) : tunedFiniteSelected n = (7 / 15 : ℝ) * Real.log n ^ 2 := by
  have h63 : (63 : ℝ) ≤ Real.log n := by linarith only [hL]
  have hn : 1 < n := lt_of_lt_of_le (by norm_num only) (large_of_log63 h63)
  have hl : (126409 / 10000 : ℝ) < Real.log n := by linarith only [hL]
  rw [← tunedFinite_eq_selected hn, tunedFinite_eq_sharp_of_log hn hl, sharp_eq_selected hn]
  exact sharpSelected_eq_triangularStage 0 hn hL hU

/-- From logarithmic scale 38 billion to the next original triangular entrance, the
423/1000 candidate strictly improves the complete preceding public cutoff. -/
theorem highWindow_lt_previous_early {n : ℕ} (hL : (38000000000 : ℝ) ≤ Real.log n)
    (hU : Real.log n < 40000000000) : highWindowSelected n < highCoeffSelected n := by
  have h30 : (30000000000 : ℝ) ≤ Real.log n := by linarith only [hL]
  have h70 : (70000 : ℝ) ≤ Real.log n := by linarith only [hL]
  have h63 : (63 : ℝ) ≤ Real.log n := by linarith only [hL]
  have h45 : Real.log n < 45000000000 := by linarith only [hU]
  have hs : 0 < Real.log n ^ 2 := sq_pos_of_pos (by linarith only [hL])
  have hB : (7 / 16 : ℝ) * Real.log n ^ 2 ≤ tunedFiniteSelected n := by
    rw [tunedFinite_eq_early_window h30 hU]
    nlinarith only [hs]
  have hold := highCoeff_lower_7_16_of_finite h70 hU hB
  have hnew := highWindowSelected_le_0423 (large_of_log63 h63) hL h45
  nlinarith only [hnew, hold, hs]

/-- Below the third tuned-profile entrance, every active tuned profile has coefficient at least
`4145/10000`. Thus the same lower bound transfers through the finite guarded minimum when it
already holds for the base. This isolates the high-profile part of the prior-envelope comparison. -/
theorem tunedHigh_lower_04145 {L B : ℝ} (hU : L < 100000000000)
    (hB : (4145 / 10000 : ℝ) * L ^ 2 ≤ B) : (4145 / 10000 : ℝ) * L ^ 2 ≤ tunedHighMin L B := by
  apply tunedHigh_lower hB
  intro i hi
  fin_cases i <;>
    first
    | (change (1480000000000 : ℝ) ≤ L at hi; linarith only [hi, hU])
    |
      (norm_num only [triangularTunedProfile, triangularP04603, triangularP04145, triangularP03315,
         triangularP02992, triangularP02891, triangularP028399] at hi ⊢;
       nlinarith only [hi, hU, sq_nonneg L])

/-- On the high window below the next tuned entrance, a lower bound for the finite base
extends to the previous public envelope. The Gaussian candidates have larger quadratic
lower bounds, and the guarded tuned profiles are handled by `tunedHigh_lower_04145`. -/
theorem highCoeff_lower_of_finite {n : ℕ} (hL : (70000 : ℝ) ≤ Real.log n)
    (hU : Real.log n < 100000000000)
    (hB : (4145 / 10000 : ℝ) * Real.log n ^ 2 ≤ tunedFiniteSelected n) :
    (4145 / 10000 : ℝ) * Real.log n ^ 2 ≤ highCoeffSelected n := by
  have h63 : (63 : ℝ) ≤ Real.log n := by linarith only [hL]
  have h0 : (0 : ℝ) ≤ Real.log n := by linarith only [hL]
  have hN := large_of_log63 h63
  have hg := seededSurplusFamily_lower h63
  have ht := gaussianTight_bound_lower h0
  have hs := sq_nonneg (Real.log n)
  rw [highCoeffSelected, ite_eq_right (not_lt.mpr hN), ite_eq_left hL, fourNinthsSelectedEnvelope,
    ite_eq_right (not_lt.mpr hN), nextTunedSelected_eq_normal, nextTunedNormalSelected,
    ite_eq_right (not_lt.mpr hN), ite_eq_left h63]
  refine le_min (le_min (le_min (tunedHigh_lower_04145 hU hB) (le_min ?_ ?_)) ?_) ?_ <;>
    nlinarith only [hg, ht, hs]

/-- Between the second and third original triangular entrances, the finite selected base
is the original coefficient `21/50` times the squared logarithm. The endpoint guards have
expired there, so the existing sharp-stage identity applies. -/
theorem tunedFinite_eq_high_window {n : ℕ} (hL : (40000000000 : ℝ) ≤ Real.log n)
    (hU : Real.log n < 100000000000) : tunedFiniteSelected n = (21 / 50 : ℝ) * Real.log n ^ 2 := by
  have h63 : (63 : ℝ) ≤ Real.log n := by linarith only [hL]
  have hn : 1 < n := lt_of_lt_of_le (by norm_num only) (large_of_log63 h63)
  have hl : (126409 / 10000 : ℝ) < Real.log n := by linarith only [hL]
  rw [← tunedFinite_eq_selected hn, tunedFinite_eq_sharp_of_log hn hl, sharp_eq_selected hn]
  exact sharpSelected_eq_triangularStage 1 hn hL hU

/-- On the first new window, the selected cutoff is strictly below the previous public
cutoff provided the previous finite base has the stated quadratic lower bound. The result
combines the new coefficient with the full previous-envelope comparison. -/
theorem highWindow_lt_previous_of_finite {n : ℕ} (hL : (45000000000 : ℝ) ≤ Real.log n)
    (hU : Real.log n < 60000000000)
    (hB : (4145 / 10000 : ℝ) * Real.log n ^ 2 ≤ tunedFiniteSelected n) :
    highWindowSelected n < highCoeffSelected n := by
  have h63 : (63 : ℝ) ≤ Real.log n := by linarith only [hL]
  have h70 : (70000 : ℝ) ≤ Real.log n := by linarith only [hL]
  have h100 : Real.log n < 100000000000 := by linarith only [hU]
  have hs : 0 < Real.log n ^ 2 := sq_pos_of_pos (by linarith only [hL])
  have hnew := highWindowSelected_le_040 (large_of_log63 h63) hL hU
  have hold := highCoeff_lower_of_finite h70 h100 hB
  nlinarith only [hnew, hold, hs]

/-- Throughout the first three new high windows, the new selected cutoff is strictly
smaller than the complete preceding public envelope. The previous finite base is identified
by its sharp triangular stage, and all remaining previous candidates have been bounded below. -/
theorem highWindow_lt_previous {n : ℕ} (hL : (45000000000 : ℝ) ≤ Real.log n)
    (hU : Real.log n < 100000000000) : highWindowSelected n < highCoeffSelected n := by
  have h40 : (40000000000 : ℝ) ≤ Real.log n := by linarith only [hL]
  have h70 : (70000 : ℝ) ≤ Real.log n := by linarith only [hL]
  have h63 : (63 : ℝ) ≤ Real.log n := by linarith only [hL]
  have hN := large_of_log63 h63
  have hs : 0 < Real.log n ^ 2 := sq_pos_of_pos (by linarith only [hL])
  have hB : (4145 / 10000 : ℝ) * Real.log n ^ 2 ≤ tunedFiniteSelected n := by
    rw [tunedFinite_eq_high_window h40 hU]
    nlinarith only [hs]
  have hold := highCoeff_lower_of_finite h70 hU hB
  by_cases h80 : (80000000000 : ℝ) ≤ Real.log n
  · have hnew := highWindowSelected_le_0346 hN h80
    nlinarith only [hnew, hold, hs]
  · by_cases h60 : (60000000000 : ℝ) ≤ Real.log n
    · have hnew := highWindowSelected_le_0369 hN h60 (lt_of_not_ge h80)
      nlinarith only [hnew, hold, hs]
    · exact highWindow_lt_previous_of_finite hL (lt_of_not_ge h60) hB

end PseudoPrime.PrimeTestBounds.MillerRabin
