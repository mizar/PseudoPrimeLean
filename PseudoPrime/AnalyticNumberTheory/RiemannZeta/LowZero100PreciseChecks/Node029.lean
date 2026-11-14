/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100PrecisePhaseArithmetic

/-! # Precise finite certificate at the twenty-ninth lower endpoint -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

-- The rational Taylor and finite-sum checks require a deeper reduction stack.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 20000000 in
-- The kernel checks the precise phase interval and finite approximation at this endpoint.
/-- At `101203 / 1024`, the precise phase check succeeds and the rotated rational finite
approximation is below `-913/10000000`. Both comparisons use exact rational arithmetic. -/
theorem endpoint029_precise_check :
    endpointPrecisePhaseCheck (101203 / 1024) = true ∧
      (endpointPreciseRotated (101203 / 1024)).1 < (-913 / 10000000 : ℚ) := by
  decide +kernel

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
