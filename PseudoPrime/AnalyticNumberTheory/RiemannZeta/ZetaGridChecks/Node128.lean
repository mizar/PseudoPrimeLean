/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridSumArithmetic
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridChecks.Node128A
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridChecks.Node128B
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridChecks.Node128C
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridChecks.Node128D
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridChecks.Node128E

/-! # Kernel-checked finite grid point -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridChecks

/-- The five independently checked blocks imply the finite-sum check at
this grid point. The component calculations are imported privately. -/
theorem node128 : gridFiniteCheck 128 = true := by
  apply decide_eq_true
  rw [grid_finite_value_split]
  dsimp only [gridFiniteBlock]
  linarith only [node128A, node128B, node128C, node128D, node128E]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridChecks
