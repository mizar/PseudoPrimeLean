/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Data.Rat.Defs

/-! # Prime-power Euler row data -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- One finite prime-power row and its rational interval certificate data.
The fields give a prime base, exponent minus one, logarithm Taylor scale
and term count, logarithm endpoints and node-power intervals. A valid row
requires prime primality and a true check; block support is verified separately. -/
structure GammaFiniteEulerRow where
  prime : ℕ
  exponent : ℕ
  logScale : ℕ
  logTerms : ℕ
  logLower : ℚ
  logUpper : ℚ
  ratios : ℚ → ℚ × ℚ

/-- The natural prime-power input represented by a row.
Exponent plus one ensures a positive power. Block certificates verify
its interval membership and exclude repeated indices. -/
def GammaFiniteEulerRow.index (r : GammaFiniteEulerRow) : ℕ :=
  r.prime ^ (r.exponent + 1)

end PseudoPrime.Analysis
