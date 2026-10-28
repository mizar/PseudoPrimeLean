/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianSeededTunedAbsorption
public import PseudoPrime.PrimeTestBounds.MillerRabin.TunedWitnessEnvelope
public import PseudoPrime.PrimeTestBounds.MillerRabin.EndpointTunedComparison
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianTunedComparison
public import PseudoPrime.PrimeTestBounds.MillerRabin.TriangularTunedOrder

/-! # Tuned intervals, preserved small values and strict improvement over sharp -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- All natural inputs below 2047 retain selected value two, without arithmetic assumptions. -/
theorem tunedSelected_small_two {n : ℕ} (hN : n < 2047) : tunedSelectedEnvelope n = 2 := by
  rw [tunedSelected_eq_small (hN.trans (by norm_num only : 2047 < 3000)), smallIntervalBound,
    ite_eq_left hN]

/-- All natural inputs in the closed-open interval [2047,3000) retain selected value three. -/
theorem tunedSelected_small_three {n : ℕ} (hN : 2047 ≤ n) (hU : n < 3000) :
    tunedSelectedEnvelope n = 3 := by
  rw [tunedSelected_eq_small hU, smallIntervalBound, ite_eq_right (not_lt.mpr hN)]

/-- Prime rounding preserves two for every natural input below 2047. -/
theorem tunedPrime_small_two {n : ℕ} (hN : n < 2047) : tunedPrimeEnvelope n = 2 := by
  rw [tunedPrimeEnvelope, tunedWitness_eq_small (hN.trans (by norm_num only : 2047 < 3000)),
    smallIntervalBound, ite_eq_left hN]
  simpa only [Nat.cast_ofNat] using primeRound_prime (by decide +kernel : Nat.Prime 2)

/-- Prime rounding preserves three for every natural input in [2047,3000). -/
theorem tunedPrime_small_three {n : ℕ} (hN : 2047 ≤ n) (hU : n < 3000) :
    tunedPrimeEnvelope n = 3 := by
  rw [tunedPrimeEnvelope, tunedWitness_eq_small hU, smallIntervalBound,
    ite_eq_right (not_lt.mpr hN)]
  simpa only [Nat.cast_ofNat] using primeRound_prime (by decide +kernel : Nat.Prime 3)

/-- Above scale 63 the public witness minimum lies below the tuned Gaussian family. -/
theorem tuned_le_gaussian {n : ℕ} (hL : 63 ≤ Real.log n) :
    tunedWitnessEnvelope n ≤ Analysis.gaussianTunedFamily (Real.log n) := by
  rw [tunedWitnessEnvelope, ite_eq_right (not_lt.mpr (large_of_log63 hL))]
  exact (min_le_right _ _).trans ((min_le_left _ _).trans (le_of_eq (ite_eq_left hL)))

/-- Above scale 63 the public witness minimum lies below either tuned seeded profile. -/
theorem tuned_le_seeded {n : ℕ} (f : Bool) (hL : 63 ≤ Real.log n) :
    tunedWitnessEnvelope n ≤ Analysis.gaussianSeededTunedBound f (Real.log n) := by
  rw [tunedWitnessEnvelope, ite_eq_right (not_lt.mpr (large_of_log63 hL))]
  have hs :
    sharpGuardMin (Real.log n) (tunedFiniteWitness n) (Analysis.gaussianTunedFamily (Real.log n))
        (min (Analysis.gaussianSeededTunedBound false (Real.log n))
          (Analysis.gaussianSeededTunedBound true (Real.log n)))
        (tunedHighMin (Real.log n) (tunedFiniteWitness n)) ≤
      min (Analysis.gaussianSeededTunedBound false (Real.log n))
        (Analysis.gaussianSeededTunedBound true (Real.log n)) :=
    (min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_left _ _).trans (le_of_eq (ite_eq_left hL))))
  cases f
  · exact hs.trans (min_le_left _ _)
  · exact hs.trans (min_le_right _ _)

/-- At each triangular entrance the public witness minimum lies below that profile. -/
theorem tuned_le_triangular {n : ℕ} (i : Fin 7)
    (hL : (Analysis.triangularTunedProfile i).T ≤ Real.log n) :
    tunedWitnessEnvelope n ≤ (Analysis.triangularTunedProfile i).C * Real.log n ^ 2 := by
  have h63 : (63 : ℝ) ≤ Real.log n := by
    linarith only [(Analysis.triangularTunedProfile i).entry, hL]
  rw [tunedWitnessEnvelope, ite_eq_right (not_lt.mpr (large_of_log63 h63))]
  exact
    (min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (tunedHigh_le_profile _ _ i hL)))

/-- Each of the thirteen cap extensions strictly improves selected and rounded sharp values. -/
theorem tunedFinite_strict (f : Analysis.FinitePrimeProfile) {n : ℕ} (hn : 1 < n) (hN : 3000 ≤ n)
    (hL : (f.logCap : ℝ) < Real.log n) (hU : Real.log n ≤ f.tunedCap) :
    tunedSelectedEnvelope n < sharpSelectedEnvelope n ∧
      tunedPrimeEnvelope n < sharpPrimeEnvelope n := by
  have hb : tunedWitnessEnvelope n ≤ (f.bound : ℝ) :=
    (tunedWitness_le_finite n).trans (tunedFinite_le_profile (.finite f) hU)
  have hs := finiteTuned_strict f hn hN hL hU
  exact
    ⟨(by
        rw [← tuned_eq_selected hn]; exact hb.trans_lt hs.1),
      (primeRound_le _).trans_lt (hb.trans_lt hs.2)⟩

/-- The new fixed 79 candidate strictly improves selected and rounded sharp values
on its closed band. -/
theorem tuned79_strict {n : ℕ} (hn : 1 < n) (hN : 3000 ≤ n) (hL : 1261 / 100 ≤ Real.log n)
    (hU : Real.log n ≤ Analysis.prime79Cap) :
    tunedSelectedEnvelope n < sharpSelectedEnvelope n ∧
      tunedPrimeEnvelope n < sharpPrimeEnvelope n := by
  have hb : tunedWitnessEnvelope n ≤ (79 : ℝ) :=
    (tunedWitness_le_finite n).trans (tunedFinite_le_profile .p79 hU)
  have hs := endpoint79_strict hn hN hL hU
  exact
    ⟨(by
        rw [← tuned_eq_selected hn]; exact hb.trans_lt hs.1),
      (primeRound_le _).trans_lt (hb.trans_lt hs.2)⟩

/-- The public tuned selection strictly improves current sharp on [100,235.73]. -/
theorem tunedGaussian_strict {n : ℕ} (hn : 1 < n) (hN : 3000 ≤ n) (hL : 100 ≤ Real.log n)
    (hU : Real.log n ≤ 23573 / 100) : tunedSelectedEnvelope n < sharpSelectedEnvelope n := by
  rw [← tuned_eq_selected hn]
  exact (tuned_le_gaussian (by linarith only [hL])).trans_lt (gaussianTunedFamily_lt_sharp hN hL hU)

/-- The seven high profiles strictly improve current sharp throughout [30 billion,1.82 trillion). -/
theorem tunedHigh_strict {n : ℕ} (hn : 1 < n) (hL : (30000000000 : ℝ) ≤ Real.log n)
    (hU : Real.log n < 1820000000000) : tunedSelectedEnvelope n < sharpSelectedEnvelope n := by
  obtain ⟨i, hi, hs⟩ := triangularTuned_strict_high hn hL hU
  rw [← tuned_eq_selected hn]
  exact (tuned_le_triangular i hi).trans_lt hs

/-- The public tuned cutoff lies below the whole seeded family above its certified entrance. -/
theorem tuned_le_seededFamily {n : ℕ} (hL : 63 ≤ Real.log n) :
    tunedWitnessEnvelope n ≤ Analysis.gaussianSeededTunedFamily (Real.log n) :=
  le_min (tuned_le_seeded false hL) (tuned_le_seeded true hL)

/-- The first open seeded improvement band strictly improves the current public sharp selection.
Its upper endpoint uses the 35000 profile displacement only. -/
theorem tunedSeeded_strict_first {n : ℕ} (hn : 1 < n) (hN : 3000 ≤ n)
    (hU : Real.log n < 30000000000)
    (hS : Analysis.gaussianSeededSharpSwitch false 35000 < Real.log n)
    (hT :
      Real.log n <
        Analysis.gaussianSeededSharpSwitch false 50000 + Analysis.gaussianSeededTunedShift false) :
    tunedSelectedEnvelope n < sharpSelectedEnvelope n := by
  have hL : (240 : ℝ) ≤ Real.log n := Analysis.gaussianSeededSharp_switch35_bounds.1.le.trans hS.le
  rw [← tuned_eq_selected hn, sharpSelected_eq_seeded hN hL hU]
  exact
    (tuned_le_seededFamily (by linarith only [hL])).trans_lt
      (Analysis.seededTunedFamily_strict_first (by linarith only [hL]) hS hT)

/-- Above the last old seeded switch and below the first high entrance,
the tuned selection is strict. -/
theorem tunedSeeded_strict_last {n : ℕ} (hn : 1 < n) (hN : 3000 ≤ n) (hU : Real.log n < 30000000000)
    (hS : Analysis.gaussianSeededSharpSwitch true 50000 < Real.log n) :
    tunedSelectedEnvelope n < sharpSelectedEnvelope n := by
  have hL : (240 : ℝ) ≤ Real.log n := by
    linarith only [(Analysis.gaussianSeededSharp_switch50_bounds true).1, hS]
  rw [← tuned_eq_selected hn, sharpSelected_eq_seeded hN hL hU]
  exact
    (tuned_le_seededFamily (by linarith only [hL])).trans_lt
      (Analysis.seededTunedFamily_strict_last (by linarith only [hL]) hS)

end PseudoPrime.PrimeTestBounds.MillerRabin
