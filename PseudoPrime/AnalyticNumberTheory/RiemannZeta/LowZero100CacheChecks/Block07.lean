/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100CachedLogs

/-! # Cached logarithm identities for the terms 113 through 128 -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

-- The exact 64-term rational logarithm calculations require a deeper recursion stack.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 12000000 in
-- The kernel checks each cached value against its internal Taylor calculation.
/-- For `113 ≤ n ≤ 128`, the cached rational logarithm equals the internally computed value.
The identities are used to avoid recomputing a logarithm at every endpoint. -/
theorem endpoint_cached_log_block07 :
    ∀ n : Fin 16, endpointCachedLog (n.val + 113) = endpointPreciseLog (n.val + 113) := by
  decide +kernel

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
