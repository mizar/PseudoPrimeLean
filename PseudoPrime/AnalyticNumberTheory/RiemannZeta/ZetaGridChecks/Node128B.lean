/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridSumArithmetic

/-! # Kernel-checked finite grid-sum block -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridChecks

set_option maxRecDepth 4096 in
-- The kernel evaluates a block of at most 128 rounded rational terms.
set_option maxHeartbeats 0 in
-- Exact rational Taylor and rounding calculations are checked by the kernel.
/-- The specified rational lower bound for this finite grid-sum block. -/
theorem node128B :
    (-1 / 1000 : ℚ) ≤
      ∑ n ∈ Finset.Ico (129 : ℕ) 257, (gridPowerApprox 128 (gridLogApprox n)).1 := by
  decide +kernel

end PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridChecks
