/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100PhaseArithmetic

/-! # First finite block at the twenty-ninth lower endpoint -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

-- The exact rounded Taylor terms require a deeper reduction stack.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
-- The kernel checks the rational phase, block of power terms, and both comparisons.
/-- Block 07 of the twenty-ninth lower endpoint has the stated rotated real bounds.
The comparison uses exact rational arithmetic and is later combined with the other blocks. -/
theorem endpoint029_block07 :
    let t : ℚ := 101203 / 1024
    let p := Analysis.rationalScaledPhase (10 ^ 15) (endpointTheta t) 16 11
    let z := endpointFiniteBlock t 97 113
    (-10858789 / 100000000 : ℚ) ≤ (Analysis.rationalComplexMul p z).1 ∧
      (Analysis.rationalComplexMul p z).1 < -10858788 / 100000000 := by
  decide +kernel

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
