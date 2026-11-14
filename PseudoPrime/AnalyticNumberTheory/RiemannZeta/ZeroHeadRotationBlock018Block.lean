/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock018Data
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiRotationGridRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadOrdinate1381
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock018Walk00
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock018Walk01
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock018Walk02
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock018Walk03

/-! # Block018 phase-certificate block -/

set_option linter.privateModule false

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- All 145 sequential walks pass the block 18 logarithmic block. -/
private theorem phaseBlock018Block_walks :
    ∀ (i : Fin 29) (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (7863 / 500)
            (phase1381Lower i + (k : ℚ) * (phase1381Upper i - phase1381Lower i) / 4)
            (fun j ↦ phaseBlock018BlockLower j i) (fun j ↦ phaseBlock018BlockUpper j i) 31 =
          true := by
  intro i k hk
  fin_cases i
  · exact phaseBlock018Walk00 k hk
  · exact phaseBlock018Walk01 k hk
  · exact phaseBlock018Walk02 k hk
  · exact phaseBlock018Walk03 k hk
  · exact phaseBlock018Walk04 k hk
  · exact phaseBlock018Walk05 k hk
  · exact phaseBlock018Walk06 k hk
  · exact phaseBlock018Walk07 k hk
  · exact phaseBlock018Walk08 k hk
  · exact phaseBlock018Walk09 k hk
  · exact phaseBlock018Walk10 k hk
  · exact phaseBlock018Walk11 k hk
  · exact phaseBlock018Walk12 k hk
  · exact phaseBlock018Walk13 k hk
  · exact phaseBlock018Walk14 k hk
  · exact phaseBlock018Walk15 k hk
  · exact phaseBlock018Walk16 k hk
  · exact phaseBlock018Walk17 k hk
  · exact phaseBlock018Walk18 k hk
  · exact phaseBlock018Walk19 k hk
  · exact phaseBlock018Walk20 k hk
  · exact phaseBlock018Walk21 k hk
  · exact phaseBlock018Walk22 k hk
  · exact phaseBlock018Walk23 k hk
  · exact phaseBlock018Walk24 k hk
  · exact phaseBlock018Walk25 k hk
  · exact phaseBlock018Walk26 k hk
  · exact phaseBlock018Walk27 k hk
  · exact phaseBlock018Walk28 k hk

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
