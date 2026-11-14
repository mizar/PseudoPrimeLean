/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.LogTaylorBounds
public import PseudoPrime.Analysis.RoundedEulerProduct

/-! # Rational logarithm intervals with a narrow log-two enclosure -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Compute the lower rational Taylor endpoint for a positive argument after a power-of-two
reduction, using a `10⁻¹⁵` enclosure for `log 2`. Soundness is proved in a separate module. -/
def rationalPreciseLogLower (N : ℚ) (j n : ℕ) : ℚ :=
  (j : ℚ) * (693147180559945 / 1000000000000000) - rationalLogSeries (1 - N / 2 ^ j) n -
    rationalLogRemainder (1 - N / 2 ^ j) n

/-- Compute the upper rational Taylor endpoint for a positive argument after a power-of-two
reduction, using a `10⁻¹⁵` enclosure for `log 2`. Soundness is proved in a separate module. -/
def rationalPreciseLogUpper (N : ℚ) (j n : ℕ) : ℚ :=
  (j : ℚ) * (693147180559946 / 1000000000000000) - rationalLogSeries (1 - N / 2 ^ j) n +
    rationalLogRemainder (1 - N / 2 ^ j) n

/-- Check positivity, convergence of the Taylor series, and containment of its precise
rational endpoints in the proposed interval. Successful checks are interpreted analytically. -/
def rationalPreciseLogCheck (N : ℚ) (j n : ℕ) (lo hi : ℚ) : Bool :=
  decide
    (0 < N ∧
      |1 - N / 2 ^ j| < 1 ∧ lo ≤ rationalPreciseLogLower N j n ∧ rationalPreciseLogUpper N j n ≤ hi)

end PseudoPrime.Analysis
