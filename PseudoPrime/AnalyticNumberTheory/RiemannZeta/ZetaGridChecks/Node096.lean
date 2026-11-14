/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridSumArithmetic
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridChecks.Node096A
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridChecks.Node096B
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridChecks.Node096C
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridChecks.Node096D
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridChecks.Node096E

/-! # Kernel-checked finite grid point -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridChecks

/-- The five independently checked blocks imply the finite-sum check at
this grid point. The component calculations are imported privately. -/
theorem node096 : gridFiniteCheck 96 = true := by
  apply decide_eq_true
  rw [grid_finite_value_split]
  dsimp only [gridFiniteBlock]
  linarith only [node096A, node096B, node096C, node096D, node096E]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridChecks
