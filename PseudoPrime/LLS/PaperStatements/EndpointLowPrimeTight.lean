/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.EndpointLowPrime

/-! # Tighter rational certificates for low prime witness bounds -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

namespace LowPrimeProfile

/-- The tightRadius datum of a fixed low-prime certificate. -/
def tightRadius : LowPrimeProfile → ℚ
  | .p23 => 53851 / 10000
  | .p29 => 55677 / 10000
  | .p31 => 60827 / 10000
  | .p37 => 64031 / 10000
  | .p41 => 65574 / 10000
  | .p43 => 68556 / 10000
  | .p47 => 72801 / 10000
  | .p53 => 76811 / 10000
  | .p59 => 78102 / 10000

/-- The tightLogCap datum of a fixed low-prime certificate. -/
def tightLogCap : LowPrimeProfile → ℚ
  | .p23 => 8032 / 1000
  | .p29 => 8271 / 1000
  | .p31 => 8934 / 1000
  | .p37 => 9339 / 1000
  | .p41 => 9532 / 1000
  | .p43 => 9902 / 1000
  | .p47 => 10422 / 1000
  | .p53 => 10907 / 1000
  | .p59 => 11062 / 1000

/-- The tightLogLo datum of a fixed low-prime certificate. -/
def tightLogLo : LowPrimeProfile → ℚ
  | .p23 => 1683579 / 1000000
  | .p29 => 1716953 / 1000000
  | .p31 => 1805445 / 1000000
  | .p37 => 1856781 / 1000000
  | .p41 => 1880593 / 1000000
  | .p43 => 1925065 / 1000000
  | .p47 => 1985144 / 1000000
  | .p53 => 2038762 / 1000000
  | .p59 => 2055430 / 1000000

/-- The tightLogHi datum of a fixed low-prime certificate. -/
def tightLogHi : LowPrimeProfile → ℚ
  | .p23 => 1683706 / 1000000
  | .p29 => 1717018 / 1000000
  | .p31 => 1805453 / 1000000
  | .p37 => 1856783 / 1000000
  | .p41 => 1880595 / 1000000
  | .p43 => 1925066 / 1000000
  | .p47 => 1985145 / 1000000
  | .p53 => 2038763 / 1000000
  | .p59 => 2055431 / 1000000

end LowPrimeProfile

/-- Each rational Taylor certificate encloses the logarithm of the selected radius. -/
theorem lowPrimeTight_log_bounds (f : LowPrimeProfile) :
    (f.tightLogLo : ℝ) ≤ Real.log (f.tightRadius : ℝ) ∧
      Real.log (f.tightRadius : ℝ) ≤ (f.tightLogHi : ℝ) := by
  have hc :
    Analysis.rationalLogIntervalCheck f.tightRadius 3 8 f.tightLogLo f.tightLogHi = true := by
    cases f <;> decide +kernel
  exact Analysis.rationalLogIntervalCheck_sound hc

/-- All selected radii exceed two and their squares precede the next prime. -/
theorem lowPrimeTight_radius_bounds (f : LowPrimeProfile) :
    (2 : ℝ) ≤ f.tightRadius ∧ (f.tightRadius : ℝ) ^ 2 < f.nextPrime := by
  cases f <;>
    norm_num only [LowPrimeProfile.tightRadius, LowPrimeProfile.nextPrime, Rat.cast_div,
      Rat.cast_ofNat, Nat.cast_ofNat, and_self]

/-- The gap quadratic has nonnegative leading and linear coefficients at each cap. -/
theorem lowPrimeTight_coefficients (f : LowPrimeProfile) :
    0 ≤ lowPrimeA f.tightRadius ∧ 0 ≤ lowPrimeB f.tightLogCap f.tightRadius := by
  cases f <;>
    norm_num only [lowPrimeA, lowPrimeB, lowPrimeV, LowPrimeProfile.tightRadius,
      LowPrimeProfile.tightLogCap, Rat.cast_div, Rat.cast_ofNat, and_self]

/-- Each rational lower logarithm endpoint gives a strictly positive gap. -/
theorem lowPrimeTight_anchor (f : LowPrimeProfile) :
    0 < endpointPointwiseGap f.tightLogCap (2096 / 1831) f.tightRadius f.tightLogLo := by
  cases f <;>
    norm_num only [endpointPointwiseGap, fullEndpointEvenExactComparisonGap,
      Analysis.pointwiseReciprocalLoss, LowPrimeProfile.tightRadius, LowPrimeProfile.tightLogCap,
      LowPrimeProfile.tightLogLo, Rat.cast_div, Rat.cast_ofNat]

/-- At every level below its cap, a selected radius has positive actual pointwise gap. -/
theorem endpointLowPrimeTight_gap (f : LowPrimeProfile) {L : ℝ} (hL : L ≤ f.tightLogCap) :
    0 < endpointPointwiseGap L (2096 / 1831) f.tightRadius (Real.log f.tightRadius) := by
  have hr := lowPrimeTight_radius_bounds f
  have hy : (1 : ℝ) ≤ f.tightRadius := by linarith only [hr.1]
  have hn : (f.tightRadius : ℝ) ≠ 0 := ne_of_gt (by linarith only [hr.1])
  have hz : (0 : ℝ) ≤ f.tightLogLo := by
    cases f <;> norm_num only [LowPrimeProfile.tightLogLo, Rat.cast_div, Rat.cast_ofNat]
  apply
    pointwise_gap_from_quad (a := lowPrimeA f.tightRadius) (b :=
      lowPrimeB f.tightLogCap f.tightRadius) hL hy hz (lowPrimeTight_log_bounds f).1
      (lowPrimeTight_coefficients f).1 (lowPrimeTight_coefficients f).2
  · intro z
    rw [lowPrime_gap_quad hn, lowPrime_gap_quad hn]
    ring
  · exact lowPrimeTight_anchor f

end PseudoPrime.LLS.PaperStatements
