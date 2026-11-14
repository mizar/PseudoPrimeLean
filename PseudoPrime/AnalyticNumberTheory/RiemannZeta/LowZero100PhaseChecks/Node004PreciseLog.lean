/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100PhasePreciseArithmetic

/-! # Narrow phase logarithm interval at the fourth lower endpoint -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

-- The exact 32-term rational Taylor reduction needs a deeper recursion stack.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
-- The kernel checks the two narrow rational logarithm bounds.
/-- Exact rational arithmetic verifies the narrow logarithm check at `31155 / 1024`.
The analytic consequence of this Boolean check is proved separately. -/
theorem endpoint004_precise_log_check : endpointPhasePreciseCheck (31155 / 1024) = true := by
  decide +kernel

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
