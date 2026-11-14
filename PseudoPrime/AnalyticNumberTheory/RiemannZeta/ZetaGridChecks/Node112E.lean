/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridSumArithmetic

/-! # Kernel-checked finite grid endpoint correction -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridChecks

set_option maxRecDepth 4096 in
-- The kernel checks the rounded rational endpoint correction.
set_option maxHeartbeats 0 in
-- Exact rational Taylor and rounding calculations are checked by the kernel.
/-- The specified rational lower bound for the endpoint correction. -/
theorem node112E :
    (-1 / 1000 : ℚ) ≤
      (Analysis.rationalComplexMul (gridEndpointCoeff 112)
          (gridPowerApprox 112 (gridLogApprox 512))).1 := by
  decide +kernel

end PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridChecks
