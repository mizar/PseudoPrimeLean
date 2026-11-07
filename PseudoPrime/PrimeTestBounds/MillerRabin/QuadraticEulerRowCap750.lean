/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerRowBlock750
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerRowSum

/-! # Scalar upper cap for a checked Euler-center block -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

-- The finite rational payload has deeply nested list expressions.
set_option maxRecDepth 20000

/-- Rational upper cap, rounded outwards to twelve decimal places.
The next theorem certifies the exact endpoint sum, independently of generation.
This scalar is used when aggregating the actual Euler finite prefix. -/
def centerRows750Upper : ℚ :=
  (130289062203 / 1000000000000)

/-- Kernel rational arithmetic verifies the sum of row upper endpoints
against the proposed cap. This is a numerical certificate, with no
floating-point premise and no repetition of the root/log checks. -/
theorem centerRows750_upper_check :
    (centerRows750.map (fun r ↦ r.hi * Analysis.gammaFiniteEulerUpper r.ratios)).sum ≤
      centerRows750Upper := by
  decide +kernel

/-- The actual Mangoldt sum on the checked rows is below the certified cap.
Apply row soundness and the rational sum certificate. This is the real
upper-bound contribution of the block to the Euler-center prefix. -/
theorem centerRows750_actual_upper :
    (centerRows750.map (fun r ↦ Analysis.gammaResolventMangoldtWeight (r.p ^ (r.k + 1)))).sum ≤
      (centerRows750Upper : ℝ) :=
  euler_rows_upper_of_rational_sum centerRows750 centerRows750Upper centerRows750_check
    centerRows750_upper_check

end PseudoPrime.PrimeTestBounds.MillerRabin
