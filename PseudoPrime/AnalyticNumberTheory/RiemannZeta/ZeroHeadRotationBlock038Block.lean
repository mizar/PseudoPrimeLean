/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock038Data
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiRotationGridRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadOrdinate1381
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock038Walk00
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock038Walk01
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock038Walk02
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock038Walk03

/-! # Block038 phase-certificate block -/

set_option linter.privateModule false

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- All 145 sequential walks pass the block 38 logarithmic block. -/
private theorem phaseBlock038Block_walks :
    ∀ (i : Fin 29) (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (9103 / 500)
            (phase1381Lower i + (k : ℚ) * (phase1381Upper i - phase1381Lower i) / 4)
            (fun j ↦ phaseBlock038BlockLower j i) (fun j ↦ phaseBlock038BlockUpper j i) 31 =
          true := by
  intro i k hk
  fin_cases i
  · exact phaseBlock038Walk00 k hk
  · exact phaseBlock038Walk01 k hk
  · exact phaseBlock038Walk02 k hk
  · exact phaseBlock038Walk03 k hk
  · exact phaseBlock038Walk04 k hk
  · exact phaseBlock038Walk05 k hk
  · exact phaseBlock038Walk06 k hk
  · exact phaseBlock038Walk07 k hk
  · exact phaseBlock038Walk08 k hk
  · exact phaseBlock038Walk09 k hk
  · exact phaseBlock038Walk10 k hk
  · exact phaseBlock038Walk11 k hk
  · exact phaseBlock038Walk12 k hk
  · exact phaseBlock038Walk13 k hk
  · exact phaseBlock038Walk14 k hk
  · exact phaseBlock038Walk15 k hk
  · exact phaseBlock038Walk16 k hk
  · exact phaseBlock038Walk17 k hk
  · exact phaseBlock038Walk18 k hk
  · exact phaseBlock038Walk19 k hk
  · exact phaseBlock038Walk20 k hk
  · exact phaseBlock038Walk21 k hk
  · exact phaseBlock038Walk22 k hk
  · exact phaseBlock038Walk23 k hk
  · exact phaseBlock038Walk24 k hk
  · exact phaseBlock038Walk25 k hk
  · exact phaseBlock038Walk26 k hk
  · exact phaseBlock038Walk27 k hk
  · exact phaseBlock038Walk28 k hk

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
