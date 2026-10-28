/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.EndpointPointwise
public import PseudoPrime.Analysis.LogTaylorBounds

/-! # Rational certificates for nine low prime witness bounds -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- The nine fixed-radius certificates for prime witness bounds 23 through 59. -/
inductive LowPrimeProfile where
  | p23
  | p29
  | p31
  | p37
  | p41
  | p43
  | p47
  | p53
  | p59
  deriving DecidableEq

namespace LowPrimeProfile

/-- The bound datum of a fixed low-prime certificate. -/
def bound : LowPrimeProfile → ℕ
  | .p23 => 23
  | .p29 => 29
  | .p31 => 31
  | .p37 => 37
  | .p41 => 41
  | .p43 => 43
  | .p47 => 47
  | .p53 => 53
  | .p59 => 59

/-- The nextPrime datum of a fixed low-prime certificate. -/
def nextPrime : LowPrimeProfile → ℕ
  | .p23 => 29
  | .p29 => 31
  | .p31 => 37
  | .p37 => 41
  | .p41 => 43
  | .p43 => 47
  | .p47 => 53
  | .p53 => 59
  | .p59 => 61

/-- The radius datum of a fixed low-prime certificate. -/
def radius : LowPrimeProfile → ℚ
  | .p23 => 269 / 50
  | .p29 => 139 / 25
  | .p31 => 152 / 25
  | .p37 => 32 / 5
  | .p41 => 131 / 20
  | .p43 => 137 / 20
  | .p47 => 182 / 25
  | .p53 => 192 / 25
  | .p59 => 781 / 100

/-- The logCap datum of a fixed low-prime certificate. -/
def logCap : LowPrimeProfile → ℚ
  | .p23 => 401 / 50
  | .p29 => 413 / 50
  | .p31 => 893 / 100
  | .p37 => 933 / 100
  | .p41 => 238 / 25
  | .p43 => 989 / 100
  | .p47 => 521 / 50
  | .p53 => 109 / 10
  | .p59 => 553 / 50

/-- The logLo datum of a fixed low-prime certificate. -/
def logLo : LowPrimeProfile → ℚ
  | .p23 => 1682630 / 1000000
  | .p29 => 1715568 / 1000000
  | .p31 => 1805001 / 1000000
  | .p37 => 1856297 / 1000000
  | .p41 => 1879464 / 1000000
  | .p43 => 1924248 / 1000000
  | .p47 => 1985130 / 1000000
  | .p53 => 2038619 / 1000000
  | .p59 => 2055404 / 1000000

/-- The logHi datum of a fixed low-prime certificate. -/
def logHi : LowPrimeProfile → ℚ
  | .p23 => 1682760 / 1000000
  | .p29 => 1715635 / 1000000
  | .p31 => 1805009 / 1000000
  | .p37 => 1856299 / 1000000
  | .p41 => 1879466 / 1000000
  | .p43 => 1924249 / 1000000
  | .p47 => 1985131 / 1000000
  | .p53 => 2038620 / 1000000
  | .p59 => 2055405 / 1000000

end LowPrimeProfile

/-- The constant reciprocal contribution in the pointwise quadratic gap. -/
noncomputable def lowPrimeV (L y : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (y ^ 2 - 1) * (L - 2096 / 1831) + 14918 / 25000 * y ^ 2 + 231 / 5000 * y -
    8891 / 18000

/-- The coefficient of the squared logarithm in the pointwise gap. -/
noncomputable def lowPrimeA (y : ℝ) : ℝ :=
  6 * y ^ 2 - 4 * y - 2

/-- The coefficient of the logarithm in the pointwise gap at level L. -/
noncomputable def lowPrimeB (L y : ℝ) : ℝ :=
  -(y - 1) ^ 2 * (L - 2096 / 1831 + 3103 / 1000) - 2 * lowPrimeV L y + 4 * (y + 1) * (y ^ 2 - 1)

/-- The constant coefficient of the pointwise gap at level L. -/
noncomputable def lowPrimeC (L y : ℝ) : ℝ :=
  (y - 1) ^ 2 * (y ^ 2 - y / 20 - 731 / 500) - 2 * (y + 1) * lowPrimeV L y

/-- For nonzero radius the existing pointwise gap is a quadratic in its log argument. -/
theorem lowPrime_gap_quad {y : ℝ} (hy : y ≠ 0) (L z : ℝ) :
    endpointPointwiseGap L (2096 / 1831) y z =
      lowPrimeA y * z ^ 2 + lowPrimeB L y * z + lowPrimeC L y := by
  dsimp only [endpointPointwiseGap, fullEndpointEvenExactComparisonGap,
    Analysis.pointwiseReciprocalLoss, lowPrimeA, lowPrimeB, lowPrimeC, lowPrimeV]
  field_simp [hy]
  ring

/-- Each rational Taylor certificate encloses the logarithm of the selected radius. -/
theorem lowPrime_log_bounds (f : LowPrimeProfile) :
    (f.logLo : ℝ) ≤ Real.log (f.radius : ℝ) ∧ Real.log (f.radius : ℝ) ≤ (f.logHi : ℝ) := by
  have hc : Analysis.rationalLogIntervalCheck f.radius 3 8 f.logLo f.logHi = true := by
    cases f <;> decide +kernel
  exact Analysis.rationalLogIntervalCheck_sound hc

/-- All selected radii exceed two and their squares precede the next prime. -/
theorem lowPrime_radius_bounds (f : LowPrimeProfile) :
    (2 : ℝ) ≤ f.radius ∧ (f.radius : ℝ) ^ 2 < f.nextPrime := by
  cases f <;>
    norm_num only [LowPrimeProfile.radius, LowPrimeProfile.nextPrime, Rat.cast_div, Rat.cast_ofNat,
      Nat.cast_ofNat, and_self]

/-- The gap quadratic has nonnegative leading and linear coefficients at each cap. -/
theorem lowPrime_coefficients (f : LowPrimeProfile) :
    0 ≤ lowPrimeA f.radius ∧ 0 ≤ lowPrimeB f.logCap f.radius := by
  cases f <;>
    norm_num only [lowPrimeA, lowPrimeB, lowPrimeV, LowPrimeProfile.radius, LowPrimeProfile.logCap,
      Rat.cast_div, Rat.cast_ofNat, and_self]

/-- Each rational lower logarithm endpoint gives a strictly positive gap. -/
theorem lowPrime_anchor (f : LowPrimeProfile) :
    0 < endpointPointwiseGap f.logCap (2096 / 1831) f.radius f.logLo := by
  cases f <;>
    norm_num only [endpointPointwiseGap, fullEndpointEvenExactComparisonGap,
      Analysis.pointwiseReciprocalLoss, LowPrimeProfile.radius, LowPrimeProfile.logCap,
      LowPrimeProfile.logLo, Rat.cast_div, Rat.cast_ofNat]

/-- At every level below its cap, a selected radius has positive actual pointwise gap. -/
theorem endpointLowPrime_gap (f : LowPrimeProfile) {L : ℝ} (hL : L ≤ f.logCap) :
    0 < endpointPointwiseGap L (2096 / 1831) f.radius (Real.log f.radius) := by
  have hr := lowPrime_radius_bounds f
  have hy : (1 : ℝ) ≤ f.radius := by linarith only [hr.1]
  have hn : (f.radius : ℝ) ≠ 0 := ne_of_gt (by linarith only [hr.1])
  have hz : (0 : ℝ) ≤ f.logLo := by
    cases f <;> norm_num only [LowPrimeProfile.logLo, Rat.cast_div, Rat.cast_ofNat]
  apply
    pointwise_gap_from_quad (a := lowPrimeA f.radius) (b := lowPrimeB f.logCap f.radius) hL hy hz
      (lowPrime_log_bounds f).1 (lowPrime_coefficients f).1 (lowPrime_coefficients f).2
  · intro z
    rw [lowPrime_gap_quad hn, lowPrime_gap_quad hn]
    ring
  · exact lowPrime_anchor f

end PseudoPrime.LLS.PaperStatements
