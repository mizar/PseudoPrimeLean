/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100PrecisePhaseArithmetic

/-! # Precise finite certificate at the fourth lower endpoint -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

-- The rational Taylor and finite-sum checks require a deeper reduction stack.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 20000000 in
-- The kernel checks the precise phase interval and finite approximation at this endpoint.
/-- At `31155 / 1024`, the precise phase check succeeds and the rotated rational finite
approximation exceeds `913/10000000`. Both comparisons use exact rational arithmetic. -/
theorem endpoint004_precise_check :
    endpointPrecisePhaseCheck (31155 / 1024) = true ∧
      (913 / 10000000 : ℚ) < (endpointPreciseRotated (31155 / 1024)).1 := by
  decide +kernel

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
