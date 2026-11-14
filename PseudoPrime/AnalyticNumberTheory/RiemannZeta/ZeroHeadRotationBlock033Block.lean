/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock033Data
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiRotationGridRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadOrdinate1381
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock033Walk00
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock033Walk01
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock033Walk02
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock033Walk03

/-! # Block033 phase-certificate block -/

set_option linter.privateModule false

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- All 145 sequential walks pass the block 33 logarithmic block. -/
private theorem phaseBlock033Block_walks :
    ∀ (i : Fin 29) (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (8793 / 500)
            (phase1381Lower i + (k : ℚ) * (phase1381Upper i - phase1381Lower i) / 4)
            (fun j ↦ phaseBlock033BlockLower j i) (fun j ↦ phaseBlock033BlockUpper j i) 31 =
          true := by
  intro i k hk
  fin_cases i
  · exact phaseBlock033Walk00 k hk
  · exact phaseBlock033Walk01 k hk
  · exact phaseBlock033Walk02 k hk
  · exact phaseBlock033Walk03 k hk
  · exact phaseBlock033Walk04 k hk
  · exact phaseBlock033Walk05 k hk
  · exact phaseBlock033Walk06 k hk
  · exact phaseBlock033Walk07 k hk
  · exact phaseBlock033Walk08 k hk
  · exact phaseBlock033Walk09 k hk
  · exact phaseBlock033Walk10 k hk
  · exact phaseBlock033Walk11 k hk
  · exact phaseBlock033Walk12 k hk
  · exact phaseBlock033Walk13 k hk
  · exact phaseBlock033Walk14 k hk
  · exact phaseBlock033Walk15 k hk
  · exact phaseBlock033Walk16 k hk
  · exact phaseBlock033Walk17 k hk
  · exact phaseBlock033Walk18 k hk
  · exact phaseBlock033Walk19 k hk
  · exact phaseBlock033Walk20 k hk
  · exact phaseBlock033Walk21 k hk
  · exact phaseBlock033Walk22 k hk
  · exact phaseBlock033Walk23 k hk
  · exact phaseBlock033Walk24 k hk
  · exact phaseBlock033Walk25 k hk
  · exact phaseBlock033Walk26 k hk
  · exact phaseBlock033Walk27 k hk
  · exact phaseBlock033Walk28 k hk

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
