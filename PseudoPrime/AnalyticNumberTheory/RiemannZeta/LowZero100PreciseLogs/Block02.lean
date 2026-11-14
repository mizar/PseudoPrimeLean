/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100PreciseLogArithmetic

/-! # Precise logarithm checks for the terms 33 through 48 -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

-- The 64-term exact rational Taylor checks require a deeper recursion stack.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 12000000 in
-- Sixteen finite logarithm enclosures are checked by the kernel.
/-- Every integer `33 ≤ n ≤ 48` passes the precise rational logarithm check.
This block is reused at all low-zero endpoints. -/
theorem endpoint_precise_log_block02 :
    ∀ n : Fin 16, endpointPreciseLogCheck (n.val + 33) = true := by decide +kernel

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
