/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridSumArithmetic
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridChecks.Node080A
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridChecks.Node080B
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridChecks.Node080C
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridChecks.Node080D
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridChecks.Node080E

/-! # Kernel-checked finite grid point -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridChecks

/-- The five independently checked blocks imply the finite-sum check at
this grid point. The component calculations are imported privately. -/
theorem node080 : gridFiniteCheck 80 = true := by
  apply decide_eq_true
  rw [grid_finite_value_split]
  dsimp only [gridFiniteBlock]
  linarith only [node080A, node080B, node080C, node080D, node080E]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridChecks
