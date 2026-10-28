/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.TunedIntervalSelection
public import PseudoPrime.PrimeTestBounds.MillerRabin.TunedWitnessEnvelope
public import PseudoPrime.PrimeTestBounds.MillerRabin.EndpointTunedOrder
public import PseudoPrime.Analysis.GaussianTunedOrder
public import PseudoPrime.Analysis.GaussianSeededTunedOrder

/-! # Normal-domain order of the tuned public envelopes -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The whole tuned Gaussian family retains a common numerical floor of 8000. -/
theorem tunedGaussian_floor8000 (L : ℝ) : (8000 : ℝ) ≤ Analysis.gaussianTunedFamily L := by
  have hf (f : Analysis.GaussianTunedProfile) : (8000 : ℝ) ≤ f.bound L :=
    (by norm_num only : (8000 : ℝ) ≤ (6 / 5) * ((91 / 10) ^ 2) ^ 2).trans
      (gaussianTuned_cutoff_floor f L)
  exact le_min (hf .low) (le_min (hf .bridge) (le_min (hf .middle) (hf .upper)))

/-- Below the first high entrance the exact public selection is the minimum of three monotone parts.
Certified floors remove the scale-63 guard even before its analytic entrance. -/
theorem tunedSelected_eq_regular {n : ℕ} (hN : 3000 ≤ n) (hU : Real.log n < 30000000000) :
    tunedSelectedEnvelope n =
      min (tunedFiniteSelected n)
        (min (Analysis.gaussianTunedFamily (Real.log n))
          (Analysis.gaussianSeededTunedFamily (Real.log n))) := by
  have hn : 1 < n := (by norm_num only : 1 < 3000).trans_le hN
  rw [← tuned_eq_selected hn, ← tunedFinite_eq_selected hn]
  rw [tunedWitnessEnvelope, ite_eq_right (not_lt.mpr hN), tunedHigh_eq_base hU]
  by_cases h63 : 63 ≤ Real.log n
  · simp only [sharpGuardMin, ite_eq_left h63, Analysis.gaussianSeededTunedFamily, min_assoc,
      min_comm, min_left_comm, min_self]
  · have hlow : Real.log n < 63 := lt_of_not_ge h63
    have h8 := Analysis.eight_lt_log_level hN
    have hP := LLS.PaperStatements.pointwiseCutoff_lt_square h8
    have hsq : Real.log n ^ 2 < (3969 : ℝ) := by nlinarith only [h8, hlow]
    have hb : tunedFiniteWitness n ≤ LLS.PaperStatements.pointwiseCutoff (Real.log n) := by
      apply (tunedFiniteWitness_le_sharp hn).trans
      rw [sharp_eq_selected hn, sharpSelected_eq_regular hN hU]
      exact (min_le_left _ _).trans (lowFinitePointwise_le_base _)
    have hG := tunedGaussian_floor8000 (Real.log n)
    have hS := Analysis.seededTunedFamily_floor (Real.log n)
    have he :
      min (tunedFiniteWitness n)
          (min (Analysis.gaussianTunedFamily (Real.log n))
            (Analysis.gaussianSeededTunedFamily (Real.log n))) =
        tunedFiniteWitness n :=
      min_eq_left (le_min (by linarith only [hb, hP, hsq, hG]) (by linarith only [hb, hP, hsq, hS]))
    rw [he]
    simp only [sharpGuardMin, ite_eq_right h63, min_self]

/-- On the regular input range the public tuned selection is at least 23. -/
theorem tunedSelected_floor23 {n : ℕ} (hN : 3000 ≤ n) (hU : Real.log n < 30000000000) :
    (23 : ℝ) ≤ tunedSelectedEnvelope n := by
  rw [tunedSelected_eq_regular hN hU]
  exact
    le_min (tunedFiniteSelected_floor23 hN hU)
      (le_min ((by norm_num only : (23 : ℝ) ≤ 8000).trans (tunedGaussian_floor8000 _))
        ((by norm_num only : (23 : ℝ) ≤ 35000).trans (Analysis.seededTunedFamily_floor _)))

/-- For 9 <= m <= n below the first high entrance, the public tuned selection is nondecreasing.
Combine the monotone finite guards and analytic parts; the preserved small branches meet at 23. -/
theorem tunedSelected_mono_normal {m n : ℕ} (hm : 9 ≤ m) (hmn : m ≤ n)
    (hU : Real.log n < 30000000000) : tunedSelectedEnvelope m ≤ tunedSelectedEnvelope n := by
  have hm1 : 1 < m := lt_of_lt_of_le (by decide : 1 < 9) hm
  have hn1 : 1 < n := hm1.trans_le hmn
  have hlog : Real.log (m : ℝ) ≤ Real.log (n : ℝ) :=
    Real.log_le_log (Nat.cast_pos.mpr (Nat.zero_lt_of_lt hm1)) (Nat.cast_le.mpr hmn)
  by_cases hnsmall : n < 3000
  · rw [tunedSelected_eq_small (lt_of_le_of_lt hmn hnsmall), tunedSelected_eq_small hnsmall, ←
      sharpSelected_eq_small (lt_of_le_of_lt hmn hnsmall), ← sharpSelected_eq_small hnsmall]
    exact sharpSelected_mono_normal hm hmn hU
  · have hnlarge : 3000 ≤ n := le_of_not_gt hnsmall
    by_cases hmsmall : m < 3000
    · have hfloor := tunedSelected_floor23 hnlarge hU
      by_cases hm2 : m < 2047
      · rw [tunedSelected_small_two hm2]
        linarith only [hfloor]
      · rw [tunedSelected_small_three (le_of_not_gt hm2) hmsmall]
        linarith only [hfloor]
    · rw [tunedSelected_eq_regular (le_of_not_gt hmsmall) (hlog.trans_lt hU),
        tunedSelected_eq_regular hnlarge hU]
      exact
        min_le_min (tunedFiniteSelected_mono_normal hm hmn hU)
          (min_le_min (Analysis.gaussianTunedFamily_mono hlog)
            (Analysis.seededTunedFamily_mono hlog))

/-- Monotone prime rounding preserves order of the tuned selection on the same normal domain. -/
theorem tunedPrime_mono_normal {m n : ℕ} (hm : 9 ≤ m) (hmn : m ≤ n)
    (hU : Real.log n < 30000000000) : tunedPrimeEnvelope m ≤ tunedPrimeEnvelope n := by
  have hm1 : 1 < m := lt_of_lt_of_le (by decide : 1 < 9) hm
  have hn1 : 1 < n := hm1.trans_le hmn
  change primeRound (tunedWitnessEnvelope m) ≤ primeRound (tunedWitnessEnvelope n)
  rw [tuned_eq_selected hm1, tuned_eq_selected hn1]
  exact primeRound_mono (tunedSelected_mono_normal hm hmn hU)

end PseudoPrime.PrimeTestBounds.MillerRabin
