/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock028Data
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiRotationGridRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadOrdinate1381
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock028Walk00
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock028Walk01
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock028Walk02
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock028Walk03

/-! # Block028 phase-certificate block -/

set_option linter.privateModule false

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- All 145 sequential walks pass the block 28 logarithmic block. -/
private theorem phaseBlock028Block_walks :
    ∀ (i : Fin 29) (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (8483 / 500)
            (phase1381Lower i + (k : ℚ) * (phase1381Upper i - phase1381Lower i) / 4)
            (fun j ↦ phaseBlock028BlockLower j i) (fun j ↦ phaseBlock028BlockUpper j i) 31 =
          true := by
  intro i k hk
  fin_cases i
  · exact phaseBlock028Walk00 k hk
  · exact phaseBlock028Walk01 k hk
  · exact phaseBlock028Walk02 k hk
  · exact phaseBlock028Walk03 k hk
  · exact phaseBlock028Walk04 k hk
  · exact phaseBlock028Walk05 k hk
  · exact phaseBlock028Walk06 k hk
  · exact phaseBlock028Walk07 k hk
  · exact phaseBlock028Walk08 k hk
  · exact phaseBlock028Walk09 k hk
  · exact phaseBlock028Walk10 k hk
  · exact phaseBlock028Walk11 k hk
  · exact phaseBlock028Walk12 k hk
  · exact phaseBlock028Walk13 k hk
  · exact phaseBlock028Walk14 k hk
  · exact phaseBlock028Walk15 k hk
  · exact phaseBlock028Walk16 k hk
  · exact phaseBlock028Walk17 k hk
  · exact phaseBlock028Walk18 k hk
  · exact phaseBlock028Walk19 k hk
  · exact phaseBlock028Walk20 k hk
  · exact phaseBlock028Walk21 k hk
  · exact phaseBlock028Walk22 k hk
  · exact phaseBlock028Walk23 k hk
  · exact phaseBlock028Walk24 k hk
  · exact phaseBlock028Walk25 k hk
  · exact phaseBlock028Walk26 k hk
  · exact phaseBlock028Walk27 k hk
  · exact phaseBlock028Walk28 k hk

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
