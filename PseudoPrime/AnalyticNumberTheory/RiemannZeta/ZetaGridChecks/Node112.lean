/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridSumArithmetic
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridChecks.Node112A
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridChecks.Node112B
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridChecks.Node112C
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridChecks.Node112D
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridChecks.Node112E

/-! # Kernel-checked finite grid point -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridChecks

/-- The five independently checked blocks imply the finite-sum check at
this grid point. The component calculations are imported privately. -/
theorem node112 : gridFiniteCheck 112 = true := by
  apply decide_eq_true
  rw [grid_finite_value_split]
  dsimp only [gridFiniteBlock]
  linarith only [node112A, node112B, node112C, node112D, node112E]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridChecks
