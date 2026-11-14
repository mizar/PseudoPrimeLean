/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock024Data
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiRotationGridRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadOrdinate1381
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock024Walk00
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock024Walk01
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock024Walk02
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock024Walk03

/-! # Block024 phase-certificate block -/

set_option linter.privateModule false

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- All 145 sequential walks pass the block 24 logarithmic block. -/
private theorem phaseBlock024Block_walks :
    ∀ (i : Fin 29) (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (8235 / 500)
            (phase1381Lower i + (k : ℚ) * (phase1381Upper i - phase1381Lower i) / 4)
            (fun j ↦ phaseBlock024BlockLower j i) (fun j ↦ phaseBlock024BlockUpper j i) 31 =
          true := by
  intro i k hk
  fin_cases i
  · exact phaseBlock024Walk00 k hk
  · exact phaseBlock024Walk01 k hk
  · exact phaseBlock024Walk02 k hk
  · exact phaseBlock024Walk03 k hk
  · exact phaseBlock024Walk04 k hk
  · exact phaseBlock024Walk05 k hk
  · exact phaseBlock024Walk06 k hk
  · exact phaseBlock024Walk07 k hk
  · exact phaseBlock024Walk08 k hk
  · exact phaseBlock024Walk09 k hk
  · exact phaseBlock024Walk10 k hk
  · exact phaseBlock024Walk11 k hk
  · exact phaseBlock024Walk12 k hk
  · exact phaseBlock024Walk13 k hk
  · exact phaseBlock024Walk14 k hk
  · exact phaseBlock024Walk15 k hk
  · exact phaseBlock024Walk16 k hk
  · exact phaseBlock024Walk17 k hk
  · exact phaseBlock024Walk18 k hk
  · exact phaseBlock024Walk19 k hk
  · exact phaseBlock024Walk20 k hk
  · exact phaseBlock024Walk21 k hk
  · exact phaseBlock024Walk22 k hk
  · exact phaseBlock024Walk23 k hk
  · exact phaseBlock024Walk24 k hk
  · exact phaseBlock024Walk25 k hk
  · exact phaseBlock024Walk26 k hk
  · exact phaseBlock024Walk27 k hk
  · exact phaseBlock024Walk28 k hk

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
