/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.LogTaylorBounds

/-! # Small finite data for strengthened principal endpoint bounds -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The twenty-one prime bases used by all finite principal certificates. -/
def finitePrincipalPrimes : Finset ℕ :=
  {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73}

/-- Power-of-two reduction used by each prime logarithm certificate. -/
def principalLogScale : ℕ → ℕ
  | 2 => 1
  | 3 => 2
  | 5 => 2
  | 7 => 3
  | 11 => 4
  | 13 => 4
  | 17 => 4
  | 19 => 4
  | 23 => 5
  | 29 => 5
  | 31 => 5
  | 37 => 5
  | 41 => 5
  | 43 => 6
  | 47 => 6
  | 53 => 6
  | 59 => 6
  | 61 => 6
  | 67 => 6
  | 71 => 6
  | 73 => 6
  | _ => 0

/-- Lower rational endpoints of the prime logarithm intervals. -/
def principalLogLo : ℕ → ℚ
  | 2 => 693147 / 1000000
  | 3 => 1098607 / 1000000
  | 5 => 1609432 / 1000000
  | 7 => 1945910 / 1000000
  | 11 => 2397858 / 1000000
  | 13 => 2564949 / 1000000
  | 17 => 2833213 / 1000000
  | 19 => 2944438 / 1000000
  | 23 => 3135480 / 1000000
  | 29 => 3367295 / 1000000
  | 31 => 3433987 / 1000000
  | 37 => 3610917 / 1000000
  | 41 => 3713555 / 1000000
  | 43 => 3761141 / 1000000
  | 47 => 3850139 / 1000000
  | 53 => 3970291 / 1000000
  | 59 => 4077537 / 1000000
  | 61 => 4110873 / 1000000
  | 67 => 4204692 / 1000000
  | 71 => 4262679 / 1000000
  | 73 => 4290459 / 1000000
  | _ => 0

/-- Upper rational endpoints of the prime logarithm intervals. -/
def principalLogHi : ℕ → ℚ
  | 2 => 693148 / 1000000
  | 3 => 1098618 / 1000000
  | 5 => 1609443 / 1000000
  | 7 => 1945911 / 1000000
  | 11 => 2397942 / 1000000
  | 13 => 2564950 / 1000000
  | 17 => 2833214 / 1000000
  | 19 => 2944440 / 1000000
  | 23 => 3135512 / 1000000
  | 29 => 3367296 / 1000000
  | 31 => 3433988 / 1000000
  | 37 => 3610918 / 1000000
  | 41 => 3713587 / 1000000
  | 43 => 3761273 / 1000000
  | 47 => 3850158 / 1000000
  | 53 => 3970293 / 1000000
  | 59 => 4077538 / 1000000
  | 61 => 4110874 / 1000000
  | 67 => 4204693 / 1000000
  | 71 => 4262680 / 1000000
  | 73 => 4290460 / 1000000
  | _ => 0

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

/-- The at-most-thirty distinct prime powers used by a profile. -/
def atoms (f : FinitePrimeProfile) : Finset ℕ :=
  ({2, 3, 4, 5, 7, 8, 9, 11, 13, 16, 17, 19, 23, 25, 27, 29, 31, 32,
    37, 41, 43, 47, 49, 53, 59, 61, 64, 67, 71, 73} :
        Finset ℕ).filter
    (· < f.nextPrime)

end FinitePrimeProfile

/-- Exponent of each composite prime power in the finite payload. -/
def principalAtomExp : ℕ → ℕ
  | 4 => 2
  | 8 => 3
  | 9 => 2
  | 16 => 4
  | 25 => 2
  | 27 => 3
  | 32 => 5
  | 49 => 2
  | 64 => 6
  | _ => 1

/-- Every listed prime has a certified Taylor-eight logarithm interval. -/
theorem principalLog_bounds {p : ℕ} (hp : p ∈ finitePrincipalPrimes) :
    (principalLogLo p : ℝ) ≤ Real.log p ∧ Real.log p ≤ (principalLogHi p : ℝ) := by
  have hc :
    ∀ p ∈ finitePrincipalPrimes,
      rationalLogIntervalCheck p (principalLogScale p) 8 (principalLogLo p) (principalLogHi p) =
        true := by
    decide +kernel
  simpa only [Rat.cast_natCast] using rationalLogIntervalCheck_sound (hc p hp)

/-- The finite payload consists of distinct positive prime powers below the radius. -/
theorem principalAtom_data (f : FinitePrimeProfile) :
    ∀ m ∈ f.atoms,
      0 < m ∧
        m.minFac ∈ finitePrincipalPrimes ∧
        m.minFac.Prime ∧
        principalAtomExp m ≠ 0 ∧
        m = m.minFac ^ principalAtomExp m ∧
        (m : ℚ) ≤ f.radius ^ 2 ∧
        0 ≤ principalLogLo m.minFac ∧
        0 ≤ 2 * f.logLo - principalAtomExp m * principalLogHi m.minFac := by
  cases f <;> decide +kernel

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

/-- Rational reciprocal lower sum over the selected prime-power payload. -/
def reciprocalLower (f : FinitePrimeProfile) : ℚ :=
  ∑ m ∈ f.atoms, principalLogLo m.minFac / m * (1 - m / f.radius ^ 2)

/-- Rational smoothed lower sum over the selected prime-power payload. -/
def smoothedLower (f : FinitePrimeProfile) : ℚ :=
  ∑ m ∈ f.atoms,
    principalLogLo m.minFac * (2 * f.logLo - principalAtomExp m * principalLogHi m.minFac)

/-- The rational evaluation of the pointwise reciprocal loss at the profile radius. -/
def reciprocalLoss (f : FinitePrimeProfile) : ℚ :=
  78861 / 50000 + (231 / 5000) / f.radius - (16033 / 9000) / f.radius ^ 2

end FinitePrimeProfile

/-- All finite reciprocal lower sums cover the strengthened analytic targets. -/
theorem finitePrincipal_rec_check (f : FinitePrimeProfile) :
    2 * f.logHi - f.reciprocalLoss + f.deltaR ≤ f.reciprocalLower := by cases f <;> decide +kernel

/-- All finite smoothed lower sums cover the strengthened analytic targets. -/
theorem finitePrincipal_log_check (f : FinitePrimeProfile) :
    f.radius ^ 2 - f.radius / 20 - (1839 / 500 : ℚ) * f.logLo - 21 / 20 + f.deltaS ≤
      f.smoothedLower := by
  cases f <;> decide +kernel

/-- All thirteen payloads use twenty-one prime logarithms and at most thirty prime powers. -/
theorem finitePrincipal_payload_size (f : FinitePrimeProfile) :
    finitePrincipalPrimes.card = 21 ∧ f.atoms.card ≤ 30 := by cases f <;> decide +kernel

end PseudoPrime.Analysis
