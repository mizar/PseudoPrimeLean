/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.EndpointLowPrime
public import PseudoPrime.Analysis.LogTaylorBounds

/-! # Rational certificates for four low prime witness bounds -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- The four fixed-radius certificates for prime witness bounds 61 through 73. -/
inductive PointwiseStep where
  | p61
  | p67
  | p71
  | p73
  deriving DecidableEq

namespace PointwiseStep

/-- The bound datum of a fixed low-prime certificate. -/
def bound : PointwiseStep → ℕ
  | .p61 => 61
  | .p67 => 67
  | .p71 => 71
  | .p73 => 73

/-- The nextPrime datum of a fixed low-prime certificate. -/
def nextPrime : PointwiseStep → ℕ
  | .p61 => 67
  | .p67 => 71
  | .p71 => 73
  | .p73 => 79

/-- The radius datum of a fixed low-prime certificate. -/
def radius : PointwiseStep → ℚ
  | .p61 => 1637 / 200
  | .p67 => 337 / 40
  | .p71 => 1068 / 125
  | .p73 => 1111 / 125

/-- The logCap datum of a fixed low-prime certificate. -/
def logCap : PointwiseStep → ℚ
  | .p61 => 11509 / 1000
  | .p67 => 1179 / 100
  | .p71 => 1193 / 100
  | .p73 => 12337 / 1000

/-- The logLo datum of a fixed low-prime certificate. -/
def logLo : PointwiseStep → ℚ
  | .p61 => 2102303 / 1000000
  | .p67 => 2131203 / 1000000
  | .p71 => 2145229 / 1000000
  | .p73 => 2184702 / 1000000

/-- The logHi datum of a fixed low-prime certificate. -/
def logHi : PointwiseStep → ℚ
  | .p61 => 2102304 / 1000000
  | .p67 => 2131204 / 1000000
  | .p71 => 2145230 / 1000000
  | .p73 => 2184703 / 1000000

end PointwiseStep

/-- Each rational Taylor certificate encloses the logarithm of the selected radius. -/
theorem pointwiseStep_log_bounds (f : PointwiseStep) :
    (f.logLo : ℝ) ≤ Real.log (f.radius : ℝ) ∧ Real.log (f.radius : ℝ) ≤ (f.logHi : ℝ) := by
  have hc : Analysis.rationalLogIntervalCheck f.radius 3 8 f.logLo f.logHi = true := by
    cases f <;> decide +kernel
  exact Analysis.rationalLogIntervalCheck_sound hc

/-- All selected radii exceed two and their squares precede the next prime. -/
theorem pointwiseStep_radius_bounds (f : PointwiseStep) :
    (2 : ℝ) ≤ f.radius ∧ (f.radius : ℝ) ^ 2 < f.nextPrime := by
  cases f <;>
    norm_num only [PointwiseStep.radius, PointwiseStep.nextPrime, Rat.cast_div, Rat.cast_ofNat,
      Nat.cast_ofNat, and_self]

/-- The gap quadratic has nonnegative leading and linear coefficients at each cap. -/
theorem pointwiseStep_coefficients (f : PointwiseStep) :
    0 ≤ lowPrimeA f.radius ∧ 0 ≤ lowPrimeB f.logCap f.radius := by
  cases f <;>
    norm_num only [lowPrimeA, lowPrimeB, lowPrimeV, PointwiseStep.radius, PointwiseStep.logCap,
      Rat.cast_div, Rat.cast_ofNat, and_self]

/-- Each rational lower logarithm endpoint gives a strictly positive gap. -/
theorem pointwiseStep_anchor (f : PointwiseStep) :
    0 < endpointPointwiseGap f.logCap (2096 / 1831) f.radius f.logLo := by
  cases f <;>
    norm_num only [endpointPointwiseGap, fullEndpointEvenExactComparisonGap,
      Analysis.pointwiseReciprocalLoss, PointwiseStep.radius, PointwiseStep.logCap,
      PointwiseStep.logLo, Rat.cast_div, Rat.cast_ofNat]

/-- At every level below its cap, a selected radius has positive actual pointwise gap. -/
theorem pointwiseStep_gap (f : PointwiseStep) {L : ℝ} (hL : L ≤ f.logCap) :
    0 < endpointPointwiseGap L (2096 / 1831) f.radius (Real.log f.radius) := by
  have hr := pointwiseStep_radius_bounds f
  have hy : (1 : ℝ) ≤ f.radius := by linarith only [hr.1]
  have hn : (f.radius : ℝ) ≠ 0 := ne_of_gt (by linarith only [hr.1])
  have hz : (0 : ℝ) ≤ f.logLo := by
    cases f <;> norm_num only [PointwiseStep.logLo, Rat.cast_div, Rat.cast_ofNat]
  apply
    pointwise_gap_from_quad (a := lowPrimeA f.radius) (b := lowPrimeB f.logCap f.radius) hL hy hz
      (pointwiseStep_log_bounds f).1 (pointwiseStep_coefficients f).1
      (pointwiseStep_coefficients f).2
  · intro z
    rw [lowPrime_gap_quad hn, lowPrime_gap_quad hn]
    ring
  · exact pointwiseStep_anchor f

end PseudoPrime.LLS.PaperStatements
