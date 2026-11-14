/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridSumArithmetic
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridChecks.Node064A
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridChecks.Node064B
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridChecks.Node064C
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridChecks.Node064D
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridChecks.Node064E

/-! # Kernel-checked finite grid point -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridChecks

/-- The five independently checked blocks imply the finite-sum check at
this grid point. The component calculations are imported privately. -/
theorem node064 : gridFiniteCheck 64 = true := by
  apply decide_eq_true
  rw [grid_finite_value_split]
  dsimp only [gridFiniteBlock]
  linarith only [node064A, node064B, node064C, node064D, node064E]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridChecks
