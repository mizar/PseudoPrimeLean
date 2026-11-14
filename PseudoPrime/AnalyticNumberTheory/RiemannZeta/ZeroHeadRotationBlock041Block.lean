/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock041Data
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiRotationGridRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadOrdinate1381
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock041Walk00
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock041Walk01
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock041Walk02
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock041Walk03

/-! # Block041 phase-certificate block -/

set_option linter.privateModule false

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- All 145 sequential walks pass the block 41 logarithmic block. -/
private theorem phaseBlock041Block_walks :
    ∀ (i : Fin 29) (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (9289 / 500)
            (phase1381Lower i + (k : ℚ) * (phase1381Upper i - phase1381Lower i) / 4)
            (fun j ↦ phaseBlock041BlockLower j i) (fun j ↦ phaseBlock041BlockUpper j i) 31 =
          true := by
  intro i k hk
  fin_cases i
  · exact phaseBlock041Walk00 k hk
  · exact phaseBlock041Walk01 k hk
  · exact phaseBlock041Walk02 k hk
  · exact phaseBlock041Walk03 k hk
  · exact phaseBlock041Walk04 k hk
  · exact phaseBlock041Walk05 k hk
  · exact phaseBlock041Walk06 k hk
  · exact phaseBlock041Walk07 k hk
  · exact phaseBlock041Walk08 k hk
  · exact phaseBlock041Walk09 k hk
  · exact phaseBlock041Walk10 k hk
  · exact phaseBlock041Walk11 k hk
  · exact phaseBlock041Walk12 k hk
  · exact phaseBlock041Walk13 k hk
  · exact phaseBlock041Walk14 k hk
  · exact phaseBlock041Walk15 k hk
  · exact phaseBlock041Walk16 k hk
  · exact phaseBlock041Walk17 k hk
  · exact phaseBlock041Walk18 k hk
  · exact phaseBlock041Walk19 k hk
  · exact phaseBlock041Walk20 k hk
  · exact phaseBlock041Walk21 k hk
  · exact phaseBlock041Walk22 k hk
  · exact phaseBlock041Walk23 k hk
  · exact phaseBlock041Walk24 k hk
  · exact phaseBlock041Walk25 k hk
  · exact phaseBlock041Walk26 k hk
  · exact phaseBlock041Walk27 k hk
  · exact phaseBlock041Walk28 k hk

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
