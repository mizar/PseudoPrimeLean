/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.SharpWitnessEnvelope
public import PseudoPrime.PrimeTestBounds.MillerRabin.TriangularProfileComparison
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianLowFloorOrder

/-! # Sharp intervals, preserved small values, and current-baseline strict gains -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Every natural input below 2047 has sharp selected value two.
This exact numerical branch does not assume oddness or compositeness. -/
theorem sharpSelected_small_two {n : ℕ} (hN : n < 2047) : sharpSelectedEnvelope n = 2 := by
  rw [sharpSelected_eq_small (hN.trans (by norm_num only : 2047 < 3000)), smallIntervalBound,
    ite_eq_left hN]

/-- Every natural input in [2047,3000) has sharp selected value three.
The lower endpoint is included and the upper endpoint is excluded. -/
theorem sharpSelected_small_three {n : ℕ} (hN : 2047 ≤ n) (hU : n < 3000) :
    sharpSelectedEnvelope n = 3 := by
  rw [sharpSelected_eq_small hU, smallIntervalBound, ite_eq_right (not_lt.mpr hN)]

/-- Prime rounding preserves the value two for every natural input below 2047.
Use the exact small branch and primality of two. -/
theorem sharpPrime_small_two {n : ℕ} (hN : n < 2047) : sharpPrimeEnvelope n = 2 := by
  rw [sharpPrimeEnvelope, sharpWitness_eq_small (hN.trans (by norm_num only : 2047 < 3000)),
    smallIntervalBound, ite_eq_left hN]
  simpa only [Nat.cast_ofNat] using primeRound_prime (by decide +kernel : Nat.Prime 2)

/-- Prime rounding preserves three for every natural input in [2047,3000).
This numerical equality holds for all naturals in the interval. -/
theorem sharpPrime_small_three {n : ℕ} (hN : 2047 ≤ n) (hU : n < 3000) :
    sharpPrimeEnvelope n = 3 := by
  rw [sharpPrimeEnvelope, sharpWitness_eq_small hU, smallIntervalBound,
    ite_eq_right (not_lt.mpr hN)]
  simpa only [Nat.cast_ofNat] using primeRound_prime (by decide +kernel : Nat.Prime 3)

/-- For inputs above one, the sharp selection is below its thirteen-candidate base. -/
theorem sharpSelected_le_low {n : ℕ} (hn : 1 < n) :
    sharpSelectedEnvelope n ≤ lowFiniteSelected n := by
  rw [← sharp_eq_selected hn, ← lowFinite_eq_selected hn]
  exact sharpWitness_le_low n

/-- On its certified domain, the sharp selection is below the fine Gaussian family. -/
theorem sharpSelected_le_gaussian {n : ℕ} (hn : 1 < n) (hL : 63 ≤ Real.log n) :
    sharpSelectedEnvelope n ≤ Analysis.gaussianLowFamily (Real.log n) := by
  rw [← sharp_eq_selected hn]
  exact sharp_le_gaussian hL

/-- On its certified domain, the sharp selection is below the fine seeded family. -/
theorem sharpSelected_le_seeded {n : ℕ} (hn : 1 < n) (hL : 63 ≤ Real.log n) :
    sharpSelectedEnvelope n ≤ Analysis.gaussianSeededSharp (Real.log n) := by
  rw [← sharp_eq_selected hn]
  exact sharp_le_seeded hL

/-- On a triangular entrance, the sharp selection is below that active high profile. -/
theorem sharpSelected_le_triangular {n : ℕ} (hn : 1 < n) (i : Fin 8)
    (hL : (Analysis.triangularProfile i).T ≤ Real.log n) :
    sharpSelectedEnvelope n ≤ (Analysis.triangularProfile i).C * Real.log n ^ 2 := by
  rw [← sharp_eq_selected hn]
  exact sharp_le_triangular i hL

/-- The rounded sharp cutoff is below the rounded thirteen-candidate base.
Apply monotonicity of prime rounding to the unrounded projection. -/
theorem sharpPrime_le_round_low {n : ℕ} :
    sharpPrimeEnvelope n ≤ primeRound (lowFiniteWitness n) := by
  exact primeRound_mono (sharpWitness_le_low n)

/-- Above the small-input branch and below scale 63, only the finite base remains.
All analytic and high guards are inactive in this exact interval formula. -/
theorem sharpSelected_eq_low {n : ℕ} (hN : 3000 ≤ n) (hL : Real.log n < 63) :
    sharpSelectedEnvelope n = lowFiniteSelected n := by
  have hU : Real.log n < (30000000000 : ℝ) := by linarith only [hL]
  simp only [sharpSelectedEnvelope, ite_eq_right (not_lt.mpr hN), sharpGuardSelected,
    ite_eq_left hL, sharpHigh_eq_base hU, min_self]

/-- Between scale 63 and thirty billion, all new high guards are inactive.
The exact selection is the minimum of the finite base and the two analytic families. -/
theorem sharpSelected_eq_analytic {n : ℕ} (hN : 3000 ≤ n) (hL : 63 ≤ Real.log n)
    (hU : Real.log n < 30000000000) :
    sharpSelectedEnvelope n =
      min (lowFiniteSelected n)
        (min (Analysis.gaussianLowFamily (Real.log n))
          (Analysis.gaussianSeededSharp (Real.log n))) := by
  rw [sharpSelectedEnvelope, ite_eq_right (not_lt.mpr hN), sharpGuardSelected,
    ite_eq_right (not_lt.mpr hL), sharpHigh_eq_base hU]
  rw [min_comm (Analysis.gaussianSeededSharp (Real.log n)) (lowFiniteSelected n),
    min_left_comm (Analysis.gaussianLowFamily (Real.log n)) (lowFiniteSelected n)
      (Analysis.gaussianSeededSharp (Real.log n)),
    ← min_assoc, min_self]

/-- A strict current-baseline comparison for the finite base transfers to the sharp selection. -/
theorem sharpSelected_lt_of_low {n : ℕ} (hn : 1 < n)
    (h : lowFiniteSelected n < refinedSelectedEnvelope n) :
    sharpSelectedEnvelope n < refinedSelectedEnvelope n :=
  (sharpSelected_le_low hn).trans_lt h

/-- A strict comparison for the valid fine Gaussian family transfers to the sharp selection. -/
theorem sharpSelected_lt_of_gaussian {n : ℕ} (hn : 1 < n) (hL : 63 ≤ Real.log n)
    (h : Analysis.gaussianLowFamily (Real.log n) < refinedSelectedEnvelope n) :
    sharpSelectedEnvelope n < refinedSelectedEnvelope n :=
  (sharpSelected_le_gaussian hn hL).trans_lt h

/-- Before the current triangular entrance, both exact seeded improvement bands
strictly improve the sharp selection against the current refined selection.
The first band includes the initial part of the current 50000 plateau. -/
theorem sharpSelected_lt_refined_seeded {n : ℕ} (hn : 1 < n) (hU : Real.log n < 1100000000000)
    (hstrict :
      (Analysis.gaussianRecoveredSeededSwitch false 35000 < Real.log n ∧
          Real.log n <
            Analysis.gaussianRecoveredSeededSwitch false 50000 +
              Analysis.gaussianSeededSharpShift) ∨
        Analysis.gaussianRecoveredSeededSwitch true 50000 < Real.log n) :
    sharpSelectedEnvelope n < refinedSelectedEnvelope n := by
  have h63 : (63 : ℝ) ≤ Real.log n := by
    rcases hstrict with h | h
    · linarith only [h.1, Analysis.gaussianRecoveredSeeded_switch35_bounds.1]
    · linarith only [h, (Analysis.gaussianRecoveredSeeded_switch50_bounds true).1]
  exact (sharpSelected_le_seeded hn h63).trans_lt (seededSharp_lt_refinedSelected hn hU hstrict)

/-- From thirty billion to the current triangular entrance, the sharp selection
is strictly below the current refined selection. Use an actual valid high profile. -/
theorem sharpSelected_lt_refined_early {n : ℕ} (hn : 1 < n) (hL : 30000000000 ≤ Real.log n)
    (hU : Real.log n < 1100000000000) : sharpSelectedEnvelope n < refinedSelectedEnvelope n := by
  obtain ⟨i, hi, hs⟩ := triangularProfile_strict_early hn hL hU
  exact (sharpSelected_le_triangular hn i hi).trans_lt hs

/-- From scale 1.48 trillion onward, the sharp selection is strictly below the current one.
The independently certified triangular profile supplies the strict numerical gap. -/
theorem sharpSelected_lt_refined_high {n : ℕ} (hn : 1 < n) (hL : 1480000000000 ≤ Real.log n) :
    sharpSelectedEnvelope n < refinedSelectedEnvelope n := by
  obtain ⟨i, hi, hs⟩ := triangularProfile_strict_high hn hL
  exact (sharpSelected_le_triangular hn i hi).trans_lt hs

/-- Throughout the closed scale interval [100,235], the sharp selection strictly
improves the current refined selection through its fine Gaussian family. -/
theorem sharpSelected_lt_refined_gaussian {n : ℕ} (hn : 1 < n) (hL : 100 ≤ Real.log n)
    (hU : Real.log n ≤ 235) : sharpSelectedEnvelope n < refinedSelectedEnvelope n := by
  exact
    (sharpSelected_le_gaussian hn (by linarith only [hL])).trans_lt
      (gaussianLowFamily_lt_refined hn hL hU)

end PseudoPrime.PrimeTestBounds.MillerRabin
