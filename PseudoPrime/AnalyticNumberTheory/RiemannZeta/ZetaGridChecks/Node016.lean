/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridSumArithmetic
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridChecks.Node016A
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridChecks.Node016B
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridChecks.Node016C
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridChecks.Node016D
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridChecks.Node016E

/-! # Kernel-checked finite grid point -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridChecks

/-- The five independently checked blocks imply the finite-sum check at
this grid point. The component calculations are imported privately. -/
theorem node016 : gridFiniteCheck 16 = true := by
  apply decide_eq_true
  rw [grid_finite_value_split]
  dsimp only [gridFiniteBlock]
  linarith only [node016A, node016B, node016C, node016D, node016E]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaGridChecks
