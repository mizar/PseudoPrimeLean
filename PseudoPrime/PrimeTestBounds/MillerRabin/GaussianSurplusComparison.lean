/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GaussianPrefix1000Surplus
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianSurplusNumerics
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianBudgetBranches
public import PseudoPrime.PrimeTestBounds.MillerRabin.NextTunedIntervalSelection
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianTunedComparison
public import PseudoPrime.PrimeTestBounds.MillerRabin.TunedEnvelopeOrder

/-! # Comparisons for the thousand-term Gaussian surplus candidate

The residual, rational root tests and prime 8419 certificate belong to this MR candidate.
The old public minimum is written explicitly in the comparison statements, so strictness
compares the complete previous selection, including both certified guards and seeded branches.
This leaf stays downstream of the witness API and does not change finite certificate data.
-/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For nonnegative scales at most 101, bound the new cutoff by a rational fourth power.
A strict quadratic budget at root 9.14 certifies the upper bound used for prime rounding. -/
theorem gaussianSurplus_upper {L : ℝ} (hL : 0 ≤ L) (hU : L ≤ 101) :
    gaussianSurplusBound L < (6 / 5 : ℝ) * ((457 / 50 : ℝ) ^ 2) ^ 2 := by
  have hC : 0 ≤ gaussianMRRefinedConductor * L + 38 / 5 := by
    norm_num only [gaussianMRRefinedConductor]
    linarith only [hL]
  have hcoef : gaussianMRRefinedBeta < gaussianMRRefinedD * (457 / 50) := by
    norm_num only [gaussianMRRefinedD, gaussianMRRefinedBeta, gaussianMRRefinedMass,
      gaussianMRRefinedWidth, gaussian6FifthsIndex, gaussian6FifthsEndpoint]
  have hbudget :
    gaussianMRRefinedConductor * L + 38 / 5 + gaussianMRRefinedBeta * (457 / 50) <
      gaussianMRRefinedD * (457 / 50 : ℝ) ^ 2 := by
    norm_num only [gaussianMRRefinedD, gaussianMRRefinedConductor, gaussianMRRefinedBeta,
      gaussianMRRefinedMass, gaussianMRRefinedWidth, gaussian6FifthsIndex, gaussian6FifthsEndpoint]
    linarith only [hU]
  have hraw :=
    lowGaussian_root_lt gaussianMRRefined_coefficients.1 gaussianMRRefined_coefficients.2 hC hcoef
      hbudget
  have hroot : gaussianSurplusRoot L < (457 / 50 : ℝ) := max_lt (by norm_num only) hraw
  have hs :=
    (sq_lt_sq₀ (gaussianSurplus_root_pos L).le (by norm_num only : (0 : ℝ) ≤ 457 / 50)).mpr hroot
  have hs' := (sq_lt_sq₀ (sq_nonneg _) (by norm_num only : (0 : ℝ) ≤ (457 / 50) ^ 2)).mpr hs
  exact mul_lt_mul_of_pos_left hs' (by norm_num only : (0 : ℝ) < 6 / 5)

/-- For scales at least 100, every preserved tuned root exceeds 9.17.
The low profile uses its exact switch; the other profiles already have larger root floors. -/
theorem gaussianTuned_root_lower {L : ℝ} (hL : 100 ≤ L) (f : GaussianTunedProfile) :
    (917 / 100 : ℝ) < f.root L := by
  have h0 : (0 : ℝ) ≤ L := by linarith only [hL]
  cases f with
  | low =>
    have hswitch : gaussianLowSwitch (917 / 100) (929 / 100) < (100 : ℝ) := by
      norm_num only [gaussianLowSwitch, gaussianMRRefinedD, gaussianMRRefinedBeta,
        gaussianMRRefinedMass, gaussianMRRefinedWidth, gaussian6FifthsIndex,
        gaussian6FifthsEndpoint, gaussianMRRefinedConductor]
    have hraw :
      (917 / 100 : ℝ) <
        Analysis.gaussianBudgetRoot gaussianMRRefinedD gaussianMRRefinedBeta
          (gaussianMRRefinedConductor * L + 929 / 100) := by
      apply lt_of_not_ge
      intro hr
      have hle :=
        (gaussianLow_raw_le_iff (by norm_num only : (9 : ℝ) ≤ 917 / 100)
              (by norm_num only : (0 : ℝ) ≤ 929 / 100) h0).mp
          hr
      linarith only [hle, hswitch, hL]
    exact hraw.trans_le (le_max_right _ _)
  | bridge =>
    exact
      (by norm_num only : (917 / 100 : ℝ) < 93 / 10).trans_le
        (GaussianTunedProfile.root_floor .bridge L)
  | middle =>
    exact
      (by norm_num only : (917 / 100 : ℝ) < 237 / 25).trans_le
        (GaussianTunedProfile.root_floor .middle L)
  | upper =>
    exact
      (by norm_num only : (917 / 100 : ℝ) < 979 / 100).trans_le
        (GaussianTunedProfile.root_floor .upper L)

/-- For scales at least 100, the entire preserved Gaussian family exceeds prime 8419.
Square the common positive root bound twice and intersect the four strict inequalities. -/
theorem gaussianTunedFamily_gt8419 {L : ℝ} (hL : 100 ≤ L) : (8419 : ℝ) < gaussianTunedFamily L := by
  have hf (f : GaussianTunedProfile) : (8419 : ℝ) < f.bound L := by
    have hr := gaussianTuned_root_lower hL f
    have hs :=
      (sq_lt_sq₀ (by norm_num only : (0 : ℝ) ≤ 917 / 100)
            (GaussianTunedProfile.root_pos f L).le).mpr
        hr
    have hs' := (sq_lt_sq₀ (sq_nonneg _) (sq_nonneg _)).mpr hs
    change (8419 : ℝ) < (6 / 5 : ℝ) * (f.root L ^ 2) ^ 2
    nlinarith only [hs']
  exact lt_min (hf .low) (lt_min (hf .bridge) (lt_min (hf .middle) (hf .upper)))

/-- On log scales from 100 to 101, the complete tuned baseline is at least 8419.
Reduce the finite branch to the sharp envelope and use the Gaussian and seeded lower bounds. -/
theorem tunedEnvelope_ge8419 {n : ℕ} (hL : 100 ≤ Real.log n) (hU : Real.log n ≤ 101) :
    (8419 : ℝ) ≤ tunedWitnessEnvelope n := by
  have h63 : (63 : ℝ) ≤ Real.log n := by linarith only [hL]
  have hN := large_of_log63 h63
  have hn : 1 < n := (by norm_num only : 1 < 3000).trans_le hN
  have hG := gaussianTunedFamily_gt8419 hL
  have hF : (8419 : ℝ) ≤ tunedFiniteSelected n := by
    rw [← tunedFinite_eq_selected hn, tunedFinite_eq_sharp_of_log hn (by linarith only [hL]),
      sharp_eq_selected hn]
    exact hG.le.trans (gaussianTunedFamily_lt_sharp hN hL (by linarith only [hU])).le
  rw [tuned_eq_selected hn, tunedSelected_eq_regular hN (by linarith only [hU])]
  exact
    le_min hF
      (le_min hG.le ((by norm_num only : (8419 : ℝ) ≤ 35000).trans (seededTunedFamily_floor _)))

/-- On log scales from 100 to 101, the complete previous public minimum is at least 8419.
The fixed-79 guard is inactive; both the tuned and surplus-seeded branches have this lower bound. -/
theorem previousNext_ge8419 {n : ℕ} (hL : 100 ≤ Real.log n) (hU : Real.log n ≤ 101) :
    (8419 : ℝ) ≤
      (if n < 3000 then smallIntervalBound n
      else
        min (tunedWitnessEnvelope n)
          (min
            (if Real.log n ≤ LLS.PaperStatements.prime79PlusCap then 79 else tunedWitnessEnvelope n)
            (if 63 ≤ Real.log n then gaussianSeededSurplusFamily (Real.log n)
            else tunedWitnessEnvelope n))) := by
  have h63 : (63 : ℝ) ≤ Real.log n := by linarith only [hL]
  have hN := large_of_log63 h63
  have h79 : ¬Real.log n ≤ LLS.PaperStatements.prime79PlusCap := by
    norm_num only [LLS.PaperStatements.prime79PlusCap, Rat.cast_div, Rat.cast_ofNat]
    linarith only [hL]
  rw [ite_eq_right (not_lt.mpr hN), ite_eq_right h79, ite_eq_left h63]
  have ht := tunedEnvelope_ge8419 hL hU
  exact
    le_min ht
      (le_min ht ((by norm_num only : (8419 : ℝ) ≤ 35000).trans (seededSurplusFamily_floor _)))

/-- On log scales from 100 to 101, the updated public witness cutoff is below prime 8419.
Project its new guarded Gaussian candidate and apply the rational root upper certificate. -/
theorem nextTuned_lt8419 {n : ℕ} (hL : 100 ≤ Real.log n) (hU : Real.log n ≤ 101) :
    nextTunedWitnessEnvelope n < (8419 : ℝ) := by
  have h63 : (63 : ℝ) ≤ Real.log n := by linarith only [hL]
  have hN := large_of_log63 h63
  have hb := gaussianSurplus_upper (by linarith only [hL]) hU
  have hg : nextTunedWitnessEnvelope n ≤ gaussianSurplusBound (Real.log n) := by
    rw [nextTunedWitnessEnvelope, ite_eq_right (not_lt.mpr hN)]
    exact
      (min_le_right _ _).trans
        ((min_le_right _ _).trans ((min_le_right _ _).trans (le_of_eq (ite_eq_left h63))))
  exact hg.trans_lt (hb.trans_le (by norm_num only))

/-- On the closed log band from 100 to 101, both real and prime-rounded public cutoffs improve.
The displayed previous expression is the complete former public minimum. The new cutoff lies
below 8419, while that certified prime lies below the old cutoff and its prime rounding. -/
theorem nextTuned_strict_surplus {n : ℕ} (hL : 100 ≤ Real.log n) (hU : Real.log n ≤ 101) :
    let previous : ℝ :=
      if n < 3000 then smallIntervalBound n
      else
        min (tunedWitnessEnvelope n)
          (min
            (if Real.log n ≤ LLS.PaperStatements.prime79PlusCap then 79 else tunedWitnessEnvelope n)
            (if 63 ≤ Real.log n then gaussianSeededSurplusFamily (Real.log n)
            else tunedWitnessEnvelope n))
    nextTunedWitnessEnvelope n < previous ∧ nextTunedPrimeEnvelope n < primeRound previous := by
  dsimp only
  have hnew := nextTuned_lt8419 hL hU
  have hold := previousNext_ge8419 hL hU
  have hp : Nat.Prime 8419 := by norm_num only
  exact
    ⟨hnew.trans_le hold, ((primeRound_le _).trans_lt hnew).trans_le (prime_le_primeRound hp hold)⟩

/-- At every natural input, the updated public cutoff does not exceed the complete former minimum.
The exact small branch is preserved; nested minimum monotonicity handles every other input. -/
theorem nextTuned_le_previous (n : ℕ) :
    nextTunedWitnessEnvelope n ≤
      (if n < 3000 then smallIntervalBound n
      else
        min (tunedWitnessEnvelope n)
          (min
            (if Real.log n ≤ LLS.PaperStatements.prime79PlusCap then 79 else tunedWitnessEnvelope n)
            (if 63 ≤ Real.log n then gaussianSeededSurplusFamily (Real.log n)
            else tunedWitnessEnvelope n))) := by
  by_cases hN : n < 3000
  · rw [nextTuned_eq_small hN, ite_eq_left hN]
  · rw [nextTunedWitnessEnvelope, ite_eq_right hN, ite_eq_right hN]
    exact min_le_min le_rfl (min_le_min le_rfl (min_le_left _ _))

/-- At every real scale, the surplus cutoff does not exceed any of the four preserved profiles.
Its residual and root floor are smaller; monotone positive roots can be squared twice. -/
theorem gaussianSurplus_le_profile (f : GaussianTunedProfile) (L : ℝ) :
    gaussianSurplusBound L ≤ f.bound L := by
  have hD : (38 / 5 : ℝ) ≤ f.residual := by
    cases f <;> norm_num only [GaussianTunedProfile.residual]
  have hraw :=
    Analysis.gaussianBudgetRoot_mono (b := gaussianMRRefinedBeta) gaussianMRRefined_coefficients.1
      (show gaussianMRRefinedConductor * L + 38 / 5 ≤ gaussianMRRefinedConductor * L + f.residual
        from by linarith only [hD])
  have hr : gaussianSurplusRoot L ≤ f.root L := max_le_max (GaussianTunedProfile.signs f).1 hraw
  have hs :=
    (sq_le_sq₀ (gaussianSurplus_root_pos L).le (GaussianTunedProfile.root_pos f L).le).mpr hr
  have hs' := (sq_le_sq₀ (sq_nonneg _) (sq_nonneg _)).mpr hs
  exact mul_le_mul_of_nonneg_left hs' (by norm_num only : (0 : ℝ) ≤ 6 / 5)

/-- At every real scale, the surplus cutoff does not exceed the preserved four-profile family.
Intersect the component comparisons; this numerical order needs no GRH assumption. -/
theorem gaussianSurplus_le_family (L : ℝ) : gaussianSurplusBound L ≤ gaussianTunedFamily L := by
  exact
    le_min (gaussianSurplus_le_profile .low L)
      (le_min (gaussianSurplus_le_profile .bridge L)
        (le_min (gaussianSurplus_le_profile .middle L) (gaussianSurplus_le_profile .upper L)))

end PseudoPrime.PrimeTestBounds.MillerRabin
