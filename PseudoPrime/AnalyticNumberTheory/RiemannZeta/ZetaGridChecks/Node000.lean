/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridSumArithmetic
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridChecks.Node000A
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridChecks.Node000B
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridChecks.Node000C
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridChecks.Node000D
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridChecks.Node000E

/-! # Kernel-checked finite grid point -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridChecks

/-- The five independently checked blocks imply the finite-sum check at
this grid point. The component calculations are imported privately. -/
theorem node000 : gridFiniteCheck 0 = true := by
  apply decide_eq_true
  rw [grid_finite_value_split]
  dsimp only [gridFiniteBlock]
  linarith only [node000A, node000B, node000C, node000D, node000E]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridChecks
