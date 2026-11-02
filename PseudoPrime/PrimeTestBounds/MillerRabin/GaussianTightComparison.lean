/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.NextTunedNormalForm

/-! # Global and prime-rounded improvement of Gaussian candidate A

The historical comparison functions reproduce the complete prior public guarded minima,
including the old residual-7.6 Gaussian branch. They are not new candidates in the selection.
On the certified middle interval that entire prior minimum equals the old Gaussian cutoff.
The rational root caps and prime 8609 then give strict real, selected and rounded improvement.
No cumulative-history module is imported by this pointwise comparison leaf.
-/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For nonnegative scales through 105.5, candidate A is strictly below prime 8609.
A rational quadratic budget puts its positive clipped root below 9.2.
Square twice and compare the resulting rational fourth power with the prime cutoff. -/
theorem gaussianTight_lt8609 {L : ℝ} (hL : 0 ≤ L) (hU : L ≤ 211 / 2) :
    gaussianTightBound L < (8609 : ℝ) := by
  have hC : 0 ≤ gaussianMRRefinedConductor * L + 36 / 5 := by
    norm_num only [gaussianMRRefinedConductor]
    linarith only [hL]
  have hcoef : gaussianMRRefinedBeta < gaussianMRRefinedD * (46 / 5) := by
    norm_num only [gaussianMRRefinedD, gaussianMRRefinedBeta, gaussianMRRefinedMass,
      gaussianMRRefinedWidth, gaussian6FifthsIndex, gaussian6FifthsEndpoint]
  have hb :
    gaussianMRRefinedConductor * L + 36 / 5 + gaussianMRRefinedBeta * (46 / 5) <
      gaussianMRRefinedD * (46 / 5 : ℝ) ^ 2 := by
    norm_num only [gaussianMRRefinedD, gaussianMRRefinedConductor, gaussianMRRefinedBeta,
      gaussianMRRefinedMass, gaussianMRRefinedWidth, gaussian6FifthsIndex, gaussian6FifthsEndpoint]
    linarith only [hU]
  have hraw :=
    lowGaussian_root_lt gaussianMRRefined_coefficients.1 gaussianMRRefined_coefficients.2 hC hcoef
      hb
  have hr : gaussianTightRoot L < (46 / 5 : ℝ) := max_lt (by norm_num only) hraw
  have hs := (sq_lt_sq₀ (gaussianTight_root_pos L).le (by norm_num only : (0 : ℝ) ≤ 46 / 5)).mpr hr
  have hs' := (sq_lt_sq₀ (sq_nonneg _) (by norm_num only : (0 : ℝ) ≤ (46 / 5) ^ 2)).mpr hs
  exact
    (mul_lt_mul_of_pos_left hs' (by norm_num only : (0 : ℝ) < 6 / 5)).trans_le (by norm_num only)

/-- From scale 105, the prior residual-7.6 surplus cutoff is strictly above 8609.
A negative quadratic budget at root 9.21 puts that test root below the prior root.
Its rational fourth power separates the old and new prime-rounded selections. -/
theorem gaussianSurplus_gt8609 {L : ℝ} (hL : 105 ≤ L) : (8609 : ℝ) < gaussianSurplusBound L := by
  have hC : 0 ≤ gaussianMRRefinedConductor * L + 38 / 5 := by
    norm_num only [gaussianMRRefinedConductor]
    linarith only [hL]
  have hb :
    gaussianMRRefinedD * (921 / 100 : ℝ) ^ 2 <
      gaussianMRRefinedBeta * (921 / 100) + (gaussianMRRefinedConductor * L + 38 / 5) := by
    norm_num only [gaussianMRRefinedD, gaussianMRRefinedConductor, gaussianMRRefinedBeta,
      gaussianMRRefinedMass, gaussianMRRefinedWidth, gaussian6FifthsIndex, gaussian6FifthsEndpoint]
    linarith only [hL]
  have hraw :=
    lowGaussian_root_gt gaussianMRRefined_coefficients.1 gaussianMRRefined_coefficients.2 hC
      (by norm_num only : (0 : ℝ) ≤ 921 / 100) hb
  have hr : (921 / 100 : ℝ) < gaussianSurplusRoot L := hraw.trans_le (le_max_right _ _)
  have hs :=
    (sq_lt_sq₀ (by norm_num only : (0 : ℝ) ≤ 921 / 100) (gaussianSurplus_root_pos L).le).mpr hr
  have hs' := (sq_lt_sq₀ (by norm_num only : (0 : ℝ) ≤ (921 / 100) ^ 2) (sq_nonneg _)).mpr hs
  exact
    lt_trans (by norm_num only : (8609 : ℝ) < (6 / 5) * ((921 / 100) ^ 2) ^ 2)
      (mul_lt_mul_of_pos_left hs' (by norm_num only : (0 : ℝ) < 6 / 5))

/-- Reproduce the complete public witness expression before candidate A replaced the old surplus.
Retain the exact small branch, tuned baseline, fixed-79 guard and both surplus guards.
This frozen residual-7.6 expression is used only for whole-minimum comparisons. -/
noncomputable def priorSurplusEnvelope (n : ℕ) : ℝ :=
  if n < 3000 then smallIntervalBound n
  else
    min (tunedWitnessEnvelope n)
      (min (if Real.log n ≤ LLS.PaperStatements.prime79PlusCap then 79 else tunedWitnessEnvelope n)
        (min
          (if 63 ≤ Real.log n then gaussianSeededSurplusFamily (Real.log n)
          else tunedWitnessEnvelope n)
          (if 63 ≤ Real.log n then gaussianSurplusBound (Real.log n) else tunedWitnessEnvelope n)))

/-- Reproduce the complete selected expression before candidate A, with all prior guards.
Use the tuned selected baseline and unchanged residual-7.6 surplus cutoff.
This is the numerical historical baseline for selected-value non-worsening and strictness. -/
noncomputable def priorSurplusSelected (n : ℕ) : ℝ :=
  if n < 3000 then smallIntervalBound n
  else
    min (tunedSelectedEnvelope n)
      (min (if Real.log n ≤ LLS.PaperStatements.prime79PlusCap then 79 else tunedSelectedEnvelope n)
        (min
          (if 63 ≤ Real.log n then gaussianSeededSurplusFamily (Real.log n)
          else tunedSelectedEnvelope n)
          (if 63 ≤ Real.log n then gaussianSurplusBound (Real.log n) else tunedSelectedEnvelope n)))

/-- For inputs above one, the historical witness and selected expressions agree exactly.
Substitute the established tuned equality through their identical guarded minima. -/
theorem priorSurplus_eq_selected {n : ℕ} (hn : 1 < n) :
    priorSurplusEnvelope n = priorSurplusSelected n := by
  simp only [priorSurplusEnvelope, priorSurplusSelected, tuned_eq_selected hn]

/-- On log scales from 100 to 235.73, the prior Gaussian surplus is below the full tuned baseline.
Use the four-profile dominance, sharp comparison and seeded floor, after all finite
entrance caps have expired. This supplies a whole-baseline rather than single-branch comparison. -/
theorem gaussianSurplus_le_tuned_mid {n : ℕ} (hL : 100 ≤ Real.log n)
    (hU : Real.log n ≤ 23573 / 100) :
    gaussianSurplusBound (Real.log n) ≤ tunedWitnessEnvelope n := by
  have h63 : (63 : ℝ) ≤ Real.log n := by linarith only [hL]
  have hN := large_of_log63 h63
  have hn : 1 < n := (by norm_num only : 1 < 3000).trans_le hN
  have hG := gaussianSurplus_le_family (Real.log n)
  have hsmall := gaussianTunedFamily_lt35000 (by linarith only [hL]) hU
  rw [tuned_eq_selected hn, tunedSelected_eq_regular hN (by linarith only [hU])]
  apply le_min
  · rw [← tunedFinite_eq_selected hn, tunedFinite_eq_sharp_of_log hn (by linarith only [hL]),
      sharp_eq_selected hn]
    exact hG.trans (gaussianTunedFamily_lt_sharp hN hL hU).le
  · exact le_min hG (hG.trans (hsmall.le.trans (seededTunedFamily_floor _)))

/-- On log scales from 100 to 235.73, the complete historical minimum is its Gaussian cutoff.
The fixed-79 guard is inactive; the tuned and seeded branches are no smaller.
This equality certifies the baseline used for the new strict improvement interval. -/
theorem priorSurplus_eq_gaussian {n : ℕ} (hL : 100 ≤ Real.log n) (hU : Real.log n ≤ 23573 / 100) :
    priorSurplusEnvelope n = gaussianSurplusBound (Real.log n) := by
  have h63 : (63 : ℝ) ≤ Real.log n := by linarith only [hL]
  have hN := large_of_log63 h63
  have h79 : ¬Real.log n ≤ LLS.PaperStatements.prime79PlusCap := by
    norm_num only [LLS.PaperStatements.prime79PlusCap, Rat.cast_div, Rat.cast_ofNat]
    linarith only [hL]
  have ht := gaussianSurplus_le_tuned_mid hL hU
  have hs : gaussianSurplusBound (Real.log n) ≤ gaussianSeededSurplusFamily (Real.log n) :=
    (gaussianSurplus_le_family _).trans
      ((gaussianTunedFamily_lt35000 (by linarith only [hL]) hU).le.trans
        (seededSurplusFamily_floor _))
  simp only [priorSurplusEnvelope, ite_eq_right (not_lt.mpr hN), ite_eq_right h79, ite_eq_left h63,
    min_eq_right hs, min_eq_right ht]

/-- At every natural input, the updated canonical witness cutoff is below the complete prior min.
Candidate A replaces the old Gaussian in the identical guard and dominates it at every scale. -/
theorem nextTuned_le_priorSurplus (n : ℕ) :
    nextTunedWitnessEnvelope n ≤ priorSurplusEnvelope n := by
  by_cases hN : n < 3000
  · rw [nextTuned_eq_small hN, priorSurplusEnvelope, ite_eq_left hN]
  · rw [nextTunedWitnessEnvelope, priorSurplusEnvelope, ite_eq_right hN, ite_eq_right hN]
    apply min_le_min le_rfl
    apply min_le_min le_rfl
    apply min_le_min le_rfl
    by_cases hL : 63 ≤ Real.log n
    · rw [ite_eq_left hL, ite_eq_left hL]
      exact gaussianTight_le_surplus _
    · rw [ite_eq_right hL, ite_eq_right hL]

/-- At every natural input, the updated selected cutoff is below the complete historical selection.
Use exact equalities to transport non-worsening and preserve the small branch. -/
theorem nextSelected_le_priorSurplus (n : ℕ) :
    nextTunedSelectedEnvelope n ≤ priorSurplusSelected n := by
  by_cases hN : n < 3000
  · rw [nextTunedSelectedEnvelope, priorSurplusSelected, ite_eq_left hN, ite_eq_left hN]
  · have hn : 1 < n := (by norm_num only : 1 < 3000).trans_le (le_of_not_gt hN)
    rw [← nextTuned_eq_selected hn, ← priorSurplus_eq_selected hn]
    exact nextTuned_le_priorSurplus n

/-- At every natural input, prime rounding preserves non-worsening against the full historical min.
Apply monotonicity of primeRound to the certified real comparison. -/
theorem nextPrime_le_priorSurplus (n : ℕ) :
    nextTunedPrimeEnvelope n ≤ primeRound (priorSurplusEnvelope n) := by
  exact primeRound_mono (nextTuned_le_priorSurplus n)

/-- On log scales from 105 to 105.5, real, selected and rounded public cutoffs all improve.
The new cutoff is below prime 8609, while the complete prior minimum is above it.
Use the exact baseline equality and certify that one fixed prime inside the kernel. -/
theorem nextTuned_strict_tighter {n : ℕ} (hL : 105 ≤ Real.log n) (hU : Real.log n ≤ 211 / 2) :
    nextTunedWitnessEnvelope n < priorSurplusEnvelope n ∧
      nextTunedSelectedEnvelope n < priorSurplusSelected n ∧
      nextTunedPrimeEnvelope n < primeRound (priorSurplusEnvelope n) := by
  have h63 : (63 : ℝ) ≤ Real.log n := by linarith only [hL]
  have hn : 1 < n := (by norm_num only : 1 < 3000).trans_le (large_of_log63 h63)
  have hnew := (nextTuned_le_tight h63).trans_lt (gaussianTight_lt8609 (by linarith only [hL]) hU)
  have hold : (8609 : ℝ) < priorSurplusEnvelope n := by
    rw [priorSurplus_eq_gaussian (by linarith only [hL]) (by linarith only [hU])]
    exact gaussianSurplus_gt8609 hL
  have hw := lt_trans hnew hold
  refine ⟨hw, ?_, ?_⟩
  · rw [← nextTuned_eq_selected hn, ← priorSurplus_eq_selected hn]
    exact hw
  · exact
      ((primeRound_le _).trans_lt hnew).trans_le
        (prime_le_primeRound (by norm_num only : Nat.Prime 8609) hold.le)

end PseudoPrime.PrimeTestBounds.MillerRabin
