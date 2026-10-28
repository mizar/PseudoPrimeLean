/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.EndpointFiniteSums

/-! # Profile-specific finite principal credits and tuned logarithmic caps -/

@[expose] public section

namespace PseudoPrime.Analysis

namespace FinitePrimeProfile

/-- The tuned logarithmic cap, preserving the current cap for comparisons. -/
def tunedCap : FinitePrimeProfile → ℚ
  | .p23 => 80901 / 10000
  | .p29 => 83320 / 10000
  | .p31 => 90031 / 10000
  | .p37 => 93961 / 10000
  | .p41 => 95875 / 10000
  | .p43 => 99619 / 10000
  | .p47 => 104895 / 10000
  | .p53 => 109671 / 10000
  | .p59 => 111199 / 10000
  | .p61 => 115654 / 10000
  | .p67 => 118463 / 10000
  | .p71 => 119879 / 10000
  | .p73 => 123975 / 10000

/-- The certified reciprocal principal credit rounded down to millionths. -/
def tunedR : FinitePrimeProfile → ℚ
  | .p23 => 7385 / 1000000
  | .p29 => 7794 / 1000000
  | .p31 => 9395 / 1000000
  | .p37 => 6554 / 1000000
  | .p41 => 6072 / 1000000
  | .p43 => 6816 / 1000000
  | .p47 => 8072 / 1000000
  | .p53 => 6484 / 1000000
  | .p59 => 6009 / 1000000
  | .p61 => 5520 / 1000000
  | .p67 => 4829 / 1000000
  | .p71 => 4972 / 1000000
  | .p73 => 5757 / 1000000

/-- The certified smoothed principal credit rounded down to millionths. -/
def tunedS : FinitePrimeProfile → ℚ
  | .p23 => 597822 / 1000000
  | .p29 => 630000 / 1000000
  | .p31 => 729227 / 1000000
  | .p37 => 651721 / 1000000
  | .p41 => 648651 / 1000000
  | .p43 => 712934 / 1000000
  | .p47 => 819332 / 1000000
  | .p53 => 769482 / 1000000
  | .p59 => 755180 / 1000000
  | .p61 => 761820 / 1000000
  | .p67 => 739461 / 1000000
  | .p71 => 762726 / 1000000
  | .p73 => 856932 / 1000000

end FinitePrimeProfile

/-- Every tuned reciprocal credit is covered by the existing finite payload. -/
theorem finiteTuned_rec_check (f : FinitePrimeProfile) :
    2 * f.logHi - f.reciprocalLoss + f.tunedR ≤ f.reciprocalLower := by cases f <;> decide +kernel

/-- Every tuned smoothed credit is covered by the existing finite payload. -/
theorem finiteTuned_log_check (f : FinitePrimeProfile) :
    f.radius ^ 2 - f.radius / 20 - (1839 / 500 : ℚ) * f.logLo - 21 / 20 + f.tunedS ≤
      f.smoothedLower := by
  cases f <;> decide +kernel

/-- The actual reciprocal principal sum retains the full tuned credit. -/
theorem finiteTuned_reciprocal (f : FinitePrimeProfile) :
    2 * Real.log (f.radius : ℝ) - pointwiseReciprocalLoss f.radius + f.tunedR ≤
      AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtSum ((f.radius : ℝ) ^ 2) := by
  have hc := (Rat.cast_le (K := ℝ)).mpr (finiteTuned_rec_check f)
  simp only [FinitePrimeProfile.reciprocalLoss, Rat.cast_add, Rat.cast_sub, Rat.cast_mul,
    Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow] at hc
  dsimp only [pointwiseReciprocalLoss]
  linarith only [hc, finitePrincipal_rec_sum f, (finitePrincipal_log_bounds f).2]

/-- The actual smoothed principal sum retains the full tuned credit. -/
theorem finiteTuned_smoothed (f : FinitePrimeProfile) :
    (f.radius : ℝ) ^ 2 - f.radius / 20 - (1839 / 500 : ℝ) * Real.log f.radius - 21 / 20 + f.tunedS ≤
      AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum ((f.radius : ℝ) ^ 2) := by
  have hc := (Rat.cast_le (K := ℝ)).mpr (finiteTuned_log_check f)
  simp only [Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat,
    Rat.cast_pow] at hc
  linarith only [hc, finitePrincipal_log_sum f, (finitePrincipal_log_bounds f).1]

end PseudoPrime.Analysis
