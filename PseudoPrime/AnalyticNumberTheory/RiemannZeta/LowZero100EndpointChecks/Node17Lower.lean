/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100FastArithmetic

/-! # Exact finite check for low-zero endpoint 17 lower -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

-- The rational Taylor and finite-sum checks require a deeper reduction stack.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 20000000 in
-- The kernel checks the phase interval and finite approximation at this endpoint.
/-- At endpoint 17 lower, the rational phase check succeeds and the
Horner-based finite approximation has the stated strict signed margin. -/
theorem endpoint_17_lower_check :
    endpointPrecisePhaseCheck (71215 / 1024 : ℚ) = true ∧
      (endpointFastRotated (71215 / 1024 : ℚ)).1 < (-913 / 10000000 : ℚ) := by
  decide +kernel

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
