/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianSeededCurrentOrder
public import PseudoPrime.PrimeTestBounds.MillerRabin.TriangularProfileBounds

/-! # Strict high-range comparisons with the current refined envelope -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The current recovered seeded minimum is strictly above (15/32)L².
Both certified component roots have the same strict quadratic lower bound. -/
theorem currentSeeded_quadratic_lower {L : ℝ} (hL : 63 ≤ L) :
    (15 / 32 : ℝ) * L ^ 2 < Analysis.gaussianRecoveredSeeded L := by
  rw [Analysis.gaussianRecoveredSeeded_eq_min hL]
  exact
    lt_min (Analysis.gaussianRecoveredSeeded_bound_lower hL)
      (Analysis.gaussianRecoveredSeeded_bound_lower hL)

/-- Between 1.1 and two trillion the current refined envelope is bounded
below by coefficient 0.282924. Compare every active candidate, splitting
the baseline at its existing 1.5-trillion entrance. -/
theorem refined_mid_quadratic_lower {n : ℕ} (hn : 1 < n) (hL : (1100000000000 : ℝ) ≤ Real.log n)
    (hU : Real.log n < 2000000000000) :
    (282924 / 1000000 : ℝ) * Real.log n ^ 2 ≤ refinedSelectedEnvelope n := by
  have h63 : (63 : ℝ) ≤ Real.log n := by linarith only [hL]
  have h240 : (240 : ℝ) ≤ Real.log n := by linarith only [hL]
  have hcoef : (282924 / 1000000 : ℝ) * Real.log n ^ 2 ≤ (15 / 32 : ℝ) * Real.log n ^ 2 :=
    mul_le_mul_of_nonneg_right (by norm_num only) (sq_nonneg _)
  have hS := hcoef.trans (currentSeeded_quadratic_lower h63).le
  rw [← refined_eq_selected hn]
  apply refined_lower_of_candidates
  · rw [lowPrimeTight_eq_next_of_log (by linarith only [hL])]
    by_cases hb : Real.log n < 1500000000000
    · rw [next_eq_seeded hn h240 hb]
      exact hcoef.trans (Analysis.gaussianSeededSelected_lower h63).le
    · rw [next_eq_early hn (le_of_not_gt hb) hU]
  · intro _
    exact hcoef.trans (Analysis.gaussianRecovered_bound_lower h63).le
  · intro _
    exact hS.trans (currentSeeded_le_gamma h240)
  · intro _
    exact hS
  · intro _
    exact mul_le_mul_of_nonneg_right (by norm_num only) (sq_nonneg _)
  · intro hh
    exact (not_le.mpr hU hh).elim

/-- Above two trillion the current refined envelope is bounded below by
coefficient 0.28237. The active baseline coefficient is 0.2827 and all three
analytic candidates remain above the shared seeded quadratic lower bound. -/
theorem refined_high_quadratic_lower {n : ℕ} (hn : 1 < n) (hL : (2000000000000 : ℝ) ≤ Real.log n) :
    (28237 / 100000 : ℝ) * Real.log n ^ 2 ≤ refinedSelectedEnvelope n := by
  have h63 : (63 : ℝ) ≤ Real.log n := by linarith only [hL]
  have h240 : (240 : ℝ) ≤ Real.log n := by linarith only [hL]
  have hcoef : (28237 / 100000 : ℝ) * Real.log n ^ 2 ≤ (15 / 32 : ℝ) * Real.log n ^ 2 :=
    mul_le_mul_of_nonneg_right (by norm_num only) (sq_nonneg _)
  have hS := hcoef.trans (currentSeeded_quadratic_lower h63).le
  rw [← refined_eq_selected hn]
  apply refined_lower_of_candidates
  · rw [lowPrimeTight_eq_next_of_log (by linarith only [hL]), next_eq_triangular hn hL]
    exact mul_le_mul_of_nonneg_right (by norm_num only) (sq_nonneg _)
  · intro _
    exact hcoef.trans (Analysis.gaussianRecovered_bound_lower h63).le
  · intro _
    exact hS.trans (currentSeeded_le_gamma h240)
  · intro _
    exact hS
  · intro _
    exact mul_le_mul_of_nonneg_right (by norm_num only) (sq_nonneg _)
  · intro _
    exact le_rfl

/-- On [30 billion,1.1 trillion), the first new profile is active and strictly
below the current refined envelope. The latter equals its current seeded
candidate, whose coefficient is strictly above 15/32>7/15. -/
theorem triangularProfile_strict_early {n : ℕ} (hn : 1 < n) (hL : (30000000000 : ℝ) ≤ Real.log n)
    (hU : Real.log n < 1100000000000) :
    ∃ i : Fin 8,
      (Analysis.triangularProfile i).T ≤ Real.log n ∧
        (Analysis.triangularProfile i).C * Real.log n ^ 2 < refinedSelectedEnvelope n := by
  refine ⟨0, hL, ?_⟩
  change (7 / 15 : ℝ) * Real.log n ^ 2 < refinedSelectedEnvelope n
  rw [refinedSelected_eq_currentSeeded hn (by linarith only [hL]) hU]
  have hs := currentSeeded_quadratic_lower (by linarith only [hL] : (63 : ℝ) ≤ Real.log n)
  have hp := sq_pos_of_pos (show (0 : ℝ) < Real.log n by linarith only [hL])
  nlinarith only [hs, hp]

/-- From 1.48 trillion onwards, an active new profile is strictly below the
current refined envelope. Use coefficient 0.2829 before 1.82 trillion, then
0.2823622; the current active quadratic lower bounds suffice on both bands. -/
theorem triangularProfile_strict_high {n : ℕ} (hn : 1 < n) (hL : (1480000000000 : ℝ) ≤ Real.log n) :
    ∃ i : Fin 8,
      (Analysis.triangularProfile i).T ≤ Real.log n ∧
        (Analysis.triangularProfile i).C * Real.log n ^ 2 < refinedSelectedEnvelope n := by
  have hp := sq_pos_of_pos (show (0 : ℝ) < Real.log n by linarith only [hL])
  by_cases h182 : Real.log n < 1820000000000
  · refine ⟨6, hL, ?_⟩
    change (2829 / 10000 : ℝ) * Real.log n ^ 2 < refinedSelectedEnvelope n
    have hs := refined_mid_quadratic_lower hn (by linarith only [hL]) (by linarith only [h182])
    nlinarith only [hs, hp]
  · refine ⟨7, le_of_not_gt h182, ?_⟩
    change (1411811 / 5000000 : ℝ) * Real.log n ^ 2 < refinedSelectedEnvelope n
    by_cases h2 : Real.log n < 2000000000000
    · have hs := refined_mid_quadratic_lower hn (by linarith only [hL]) h2
      nlinarith only [hs, hp]
    · have hs := refined_high_quadratic_lower hn (le_of_not_gt h2)
      nlinarith only [hs, hp]

end PseudoPrime.PrimeTestBounds.MillerRabin
