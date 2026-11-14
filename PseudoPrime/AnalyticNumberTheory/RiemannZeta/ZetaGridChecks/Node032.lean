/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridSumArithmetic
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridChecks.Node032A
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridChecks.Node032B
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridChecks.Node032C
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridChecks.Node032D
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridChecks.Node032E

/-! # Kernel-checked finite grid point -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridChecks

/-- The five independently checked blocks imply the finite-sum check at
this grid point. The component calculations are imported privately. -/
theorem node032 : gridFiniteCheck 32 = true := by
  apply decide_eq_true
  rw [grid_finite_value_split]
  dsimp only [gridFiniteBlock]
  linarith only [node032A, node032B, node032C, node032D, node032E]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridChecks
