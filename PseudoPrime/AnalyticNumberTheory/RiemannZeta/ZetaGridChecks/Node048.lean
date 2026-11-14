/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridSumArithmetic
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridChecks.Node048A
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridChecks.Node048B
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridChecks.Node048C
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridChecks.Node048D
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridChecks.Node048E

/-! # Kernel-checked finite grid point -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridChecks

/-- The five independently checked blocks imply the finite-sum check at
this grid point. The component calculations are imported privately. -/
theorem node048 : gridFiniteCheck 48 = true := by
  apply decide_eq_true
  rw [grid_finite_value_split]
  dsimp only [gridFiniteBlock]
  linarith only [node048A, node048B, node048C, node048D, node048E]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridChecks
