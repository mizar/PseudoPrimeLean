/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import PseudoPrime.Analysis.LogTaylorBounds

/-! # Scalar data for finite principal endpoint profiles -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The thirteen finite principal endpoint profiles, indexed by their prime cutoff. -/
inductive FinitePrimeProfile
  | p23
  | p29
  | p31
  | p37
  | p41
  | p43
  | p47
  | p53
  | p59
  | p61
  | p67
  | p71
  | p73
  deriving DecidableEq

namespace FinitePrimeProfile

/-- The rejecting-prime cutoff. -/
def bound : FinitePrimeProfile → ℕ
  | .p23 => 23
  | .p29 => 29
  | .p31 => 31
  | .p37 => 37
  | .p41 => 41
  | .p43 => 43
  | .p47 => 47
  | .p53 => 53
  | .p59 => 59
  | .p61 => 61
  | .p67 => 67
  | .p71 => 71
  | .p73 => 73

/-- The next prime used to round the analytic radius. -/
def nextPrime : FinitePrimeProfile → ℕ
  | .p23 => 29
  | .p29 => 31
  | .p31 => 37
  | .p37 => 41
  | .p41 => 43
  | .p43 => 47
  | .p47 => 53
  | .p53 => 59
  | .p59 => 61
  | .p61 => 67
  | .p67 => 71
  | .p71 => 73
  | .p73 => 79

/-- The current published cap, used only in strict comparisons. -/
def currentCap : FinitePrimeProfile → ℚ
  | .p23 => 1004 / 125
  | .p29 => 8271 / 1000
  | .p31 => 4467 / 500
  | .p37 => 9339 / 1000
  | .p41 => 2383 / 250
  | .p43 => 4951 / 500
  | .p47 => 5211 / 500
  | .p53 => 10907 / 1000
  | .p59 => 5531 / 500
  | .p61 => 11509 / 1000
  | .p67 => 1179 / 100
  | .p71 => 1193 / 100
  | .p73 => 12337 / 1000

/-- The strengthened logarithmic cap. -/
def logCap : FinitePrimeProfile → ℚ
  | .p23 => 8087 / 1000
  | .p29 => 333 / 40
  | .p31 => 8987 / 1000
  | .p37 => 939 / 100
  | .p41 => 9583 / 1000
  | .p43 => 1244 / 125
  | .p47 => 10471 / 1000
  | .p53 => 2191 / 200
  | .p59 => 11109 / 1000
  | .p61 => 5773 / 500
  | .p67 => 1183 / 100
  | .p71 => 1197 / 100
  | .p73 => 12373 / 1000

/-- The rational analytic test radius. -/
def radius : FinitePrimeProfile → ℚ
  | .p23 => 53851 / 10000
  | .p29 => 55677 / 10000
  | .p31 => 60827 / 10000
  | .p37 => 64031 / 10000
  | .p41 => 32787 / 5000
  | .p43 => 17139 / 2500
  | .p47 => 72801 / 10000
  | .p53 => 76811 / 10000
  | .p59 => 39051 / 5000
  | .p61 => 1637 / 200
  | .p67 => 337 / 40
  | .p71 => 1068 / 125
  | .p73 => 1111 / 125

/-- The lower radius-logarithm endpoint. -/
def logLo : FinitePrimeProfile → ℚ
  | .p23 => 1683579 / 1000000
  | .p29 => 1716953 / 1000000
  | .p31 => 361089 / 200000
  | .p37 => 1856781 / 1000000
  | .p41 => 1880593 / 1000000
  | .p43 => 385013 / 200000
  | .p47 => 248143 / 125000
  | .p53 => 1019381 / 500000
  | .p59 => 205543 / 100000
  | .p61 => 2102303 / 1000000
  | .p67 => 2131203 / 1000000
  | .p71 => 2145229 / 1000000
  | .p73 => 1092351 / 500000

/-- The upper radius-logarithm endpoint. -/
def logHi : FinitePrimeProfile → ℚ
  | .p23 => 841853 / 500000
  | .p29 => 858509 / 500000
  | .p31 => 1805453 / 1000000
  | .p37 => 1856783 / 1000000
  | .p41 => 376119 / 200000
  | .p43 => 962533 / 500000
  | .p47 => 397029 / 200000
  | .p53 => 2038763 / 1000000
  | .p59 => 2055431 / 1000000
  | .p61 => 65697 / 31250
  | .p67 => 532801 / 250000
  | .p71 => 214523 / 100000
  | .p73 => 2184703 / 1000000

/-- The reciprocal principal gain; the last four profiles use the weaker gain. -/
def deltaR (f : FinitePrimeProfile) : ℚ :=
  if f.bound ≤ 59 then 3 / 500 else 1 / 250

/-- The smoothed principal gain; the last four profiles use the weaker gain. -/
def deltaS (f : FinitePrimeProfile) : ℚ :=
  if f.bound ≤ 59 then 59 / 100 else 1 / 2

end FinitePrimeProfile

/-- Every profile radius has a certified Taylor-eight logarithm interval. -/
theorem finitePrincipal_log_bounds (f : FinitePrimeProfile) :
    (f.logLo : ℝ) ≤ Real.log (f.radius : ℝ) ∧ Real.log (f.radius : ℝ) ≤ (f.logHi : ℝ) := by
  have hc : rationalLogIntervalCheck f.radius 3 8 f.logLo f.logHi = true := by
    cases f <;> decide +kernel
  exact rationalLogIntervalCheck_sound hc

/-- The rational radius is at least two and precedes the next prime. -/
theorem finitePrincipal_radius_bounds (f : FinitePrimeProfile) :
    (2 : ℝ) ≤ f.radius ∧ (f.radius : ℝ) ^ 2 < f.nextPrime := by
  cases f <;>
    norm_num only [FinitePrimeProfile.radius, FinitePrimeProfile.nextPrime, Rat.cast_div,
      Rat.cast_ofNat, Nat.cast_ofNat, and_self]

namespace FinitePrimeProfile

/-- The rational evaluation of the pointwise reciprocal loss at the profile radius. -/
def reciprocalLoss (f : FinitePrimeProfile) : ℚ :=
  78861 / 50000 + (231 / 5000) / f.radius - (16033 / 9000) / f.radius ^ 2

end FinitePrimeProfile

end PseudoPrime.Analysis
