/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100PhaseArithmetic

/-! # Euler–Maclaurin correction at the twenty-ninth lower endpoint -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

-- Exact rounded Taylor and rational correction arithmetic require a deeper reduction stack.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
-- The kernel checks the phase, correction term, and rational comparisons.
/-- The rotated correction at `101203 / 1024` lies in the stated rational interval.
It completes the blockwise finite-sum certificate at this endpoint. -/
theorem endpoint029_correction :
    let t : ℚ := 101203 / 1024
    let p := Analysis.rationalScaledPhase (10 ^ 15) (endpointTheta t) 16 11
    let z := endpointFiniteCorrection t
    (1081848 / 100000000 : ℚ) ≤ (Analysis.rationalComplexMul p z).1 ∧
      (Analysis.rationalComplexMul p z).1 < 1081849 / 100000000 := by
  decide +kernel

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
