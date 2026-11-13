/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.LogTaylorBounds
public import PseudoPrime.Analysis.EndpointFiniteProfile

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

namespace FinitePrimeProfile

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

namespace FinitePrimeProfile

/-- Rational reciprocal lower sum over the selected prime-power payload. -/
def reciprocalLower (f : FinitePrimeProfile) : ℚ :=
  ∑ m ∈ f.atoms, principalLogLo m.minFac / m * (1 - m / f.radius ^ 2)

/-- Rational smoothed lower sum over the selected prime-power payload. -/
def smoothedLower (f : FinitePrimeProfile) : ℚ :=
  ∑ m ∈ f.atoms,
    principalLogLo m.minFac * (2 * f.logLo - principalAtomExp m * principalLogHi m.minFac)

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
