/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock044Data
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiRotationGridRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadOrdinate1381
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock044Walk00
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock044Walk01
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock044Walk02
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock044Walk03

/-! # Block044 phase-certificate block -/

set_option linter.privateModule false

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- All 145 sequential walks pass the block 44 logarithmic block. -/
private theorem phaseBlock044Block_walks :
    ∀ (i : Fin 29) (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (9475 / 500)
            (phase1381Lower i + (k : ℚ) * (phase1381Upper i - phase1381Lower i) / 4)
            (fun j ↦ phaseBlock044BlockLower j i) (fun j ↦ phaseBlock044BlockUpper j i) 31 =
          true := by
  intro i k hk
  fin_cases i
  · exact phaseBlock044Walk00 k hk
  · exact phaseBlock044Walk01 k hk
  · exact phaseBlock044Walk02 k hk
  · exact phaseBlock044Walk03 k hk
  · exact phaseBlock044Walk04 k hk
  · exact phaseBlock044Walk05 k hk
  · exact phaseBlock044Walk06 k hk
  · exact phaseBlock044Walk07 k hk
  · exact phaseBlock044Walk08 k hk
  · exact phaseBlock044Walk09 k hk
  · exact phaseBlock044Walk10 k hk
  · exact phaseBlock044Walk11 k hk
  · exact phaseBlock044Walk12 k hk
  · exact phaseBlock044Walk13 k hk
  · exact phaseBlock044Walk14 k hk
  · exact phaseBlock044Walk15 k hk
  · exact phaseBlock044Walk16 k hk
  · exact phaseBlock044Walk17 k hk
  · exact phaseBlock044Walk18 k hk
  · exact phaseBlock044Walk19 k hk
  · exact phaseBlock044Walk20 k hk
  · exact phaseBlock044Walk21 k hk
  · exact phaseBlock044Walk22 k hk
  · exact phaseBlock044Walk23 k hk
  · exact phaseBlock044Walk24 k hk
  · exact phaseBlock044Walk25 k hk
  · exact phaseBlock044Walk26 k hk
  · exact phaseBlock044Walk27 k hk
  · exact phaseBlock044Walk28 k hk

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
