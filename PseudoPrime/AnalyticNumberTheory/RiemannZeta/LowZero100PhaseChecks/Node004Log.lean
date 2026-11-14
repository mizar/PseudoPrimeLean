/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100PhaseArithmetic

/-! # Phase logarithm check at the fourth lower endpoint -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

-- The exact 32-term rational Taylor reduction needs a deeper recursion stack.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
-- The kernel checks all rational arithmetic in the logarithm enclosure.
/-- Exact rational arithmetic checks the phase logarithm enclosure at `31155 / 1024`.
The analytic meaning of the Boolean check is proved separately. -/
theorem endpoint004_log_check : endpointPhaseLogCheck (31155 / 1024) = true := by decide +kernel

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
