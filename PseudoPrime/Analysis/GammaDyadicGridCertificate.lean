/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaExpRationalBounds

/-! # Rational grid certificate for the ramified dyadic budget -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Lower endpoint of the width-one-hundred grid covering [20000,40000]. -/
def gammaDyadicGridLower (i : ℕ) : ℚ :=
  20000 + 100 * (i : ℚ)

/-- Upper endpoint of the same dyadic scale grid. -/
def gammaDyadicGridUpper (i : ℕ) : ℚ :=
  20100 + 100 * (i : ℚ)

/-- Integer lower bound for the square root at a grid's lower endpoint. -/
def gammaDyadicGridRoot (i : ℕ) : ℕ :=
  Nat.sqrt (20000 + 100 * i)

/-- All two hundred intervals have a positive certified square-root lower
bound, a valid power-sixteen cutoff, and Taylor-prefix ramp cost at most
649/10000 using log two <=7/10. Exact rational arithmetic verifies every
interval, providing a full finite cover rather than endpoint sampling. -/
theorem gamma_dyadic_grid_checks :
    ∀ i ∈ Finset.range 200,
      0 < gammaDyadicGridRoot i ∧
        (gammaDyadicGridRoot i : ℚ) ^ 2 ≤ gammaDyadicGridLower i ∧
        (99 / 40 : ℚ) * gammaDyadicGridUpper i ≤ (2 : ℚ) ^ 17 ∧
        (7 / 10 : ℚ) * gammaDyadicExpPrefixUpper (gammaDyadicGridUpper i) 16 ≤
          (649 / 10000 : ℚ) * gammaDyadicGridRoot i := by
  decide +kernel

end PseudoPrime.Analysis
