/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock025Data
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiRotationGridRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadOrdinate1381
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock025Walk00
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock025Walk01
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock025Walk02
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock025Walk03

/-! # Block025 phase-certificate block -/

set_option linter.privateModule false

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- All 145 sequential walks pass the block 25 logarithmic block. -/
private theorem phaseBlock025Block_walks :
    ∀ (i : Fin 29) (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (8297 / 500)
            (phase1381Lower i + (k : ℚ) * (phase1381Upper i - phase1381Lower i) / 4)
            (fun j ↦ phaseBlock025BlockLower j i) (fun j ↦ phaseBlock025BlockUpper j i) 31 =
          true := by
  intro i k hk
  fin_cases i
  · exact phaseBlock025Walk00 k hk
  · exact phaseBlock025Walk01 k hk
  · exact phaseBlock025Walk02 k hk
  · exact phaseBlock025Walk03 k hk
  · exact phaseBlock025Walk04 k hk
  · exact phaseBlock025Walk05 k hk
  · exact phaseBlock025Walk06 k hk
  · exact phaseBlock025Walk07 k hk
  · exact phaseBlock025Walk08 k hk
  · exact phaseBlock025Walk09 k hk
  · exact phaseBlock025Walk10 k hk
  · exact phaseBlock025Walk11 k hk
  · exact phaseBlock025Walk12 k hk
  · exact phaseBlock025Walk13 k hk
  · exact phaseBlock025Walk14 k hk
  · exact phaseBlock025Walk15 k hk
  · exact phaseBlock025Walk16 k hk
  · exact phaseBlock025Walk17 k hk
  · exact phaseBlock025Walk18 k hk
  · exact phaseBlock025Walk19 k hk
  · exact phaseBlock025Walk20 k hk
  · exact phaseBlock025Walk21 k hk
  · exact phaseBlock025Walk22 k hk
  · exact phaseBlock025Walk23 k hk
  · exact phaseBlock025Walk24 k hk
  · exact phaseBlock025Walk25 k hk
  · exact phaseBlock025Walk26 k hk
  · exact phaseBlock025Walk27 k hk
  · exact phaseBlock025Walk28 k hk

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
