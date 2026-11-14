/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100FastArithmetic
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100PreciseChecks.Node004Fast

/-! # Exact finite check for low-zero endpoint 04 lower -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- At endpoint 04 lower, the rational phase check succeeds and the
Horner-based finite approximation has the stated strict signed margin. This reuses the
representative endpoint certificate. -/
theorem endpoint_04_lower_check :
    endpointPrecisePhaseCheck (31155 / 1024 : ℚ) = true ∧
      (913 / 10000000 : ℚ) < (endpointFastRotated (31155 / 1024 : ℚ)).1 := by
  exact endpoint004_fast_check

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
