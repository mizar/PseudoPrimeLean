/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock017Data
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiRotationGridRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadOrdinate1381
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock017Walk00
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock017Walk01
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock017Walk02
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock017Walk03

/-! # Block017 phase-certificate block -/

set_option linter.privateModule false

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- All 145 sequential walks pass the block 17 logarithmic block. -/
private theorem phaseBlock017Block_walks :
    ∀ (i : Fin 29) (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (7801 / 500)
            (phase1381Lower i + (k : ℚ) * (phase1381Upper i - phase1381Lower i) / 4)
            (fun j ↦ phaseBlock017BlockLower j i) (fun j ↦ phaseBlock017BlockUpper j i) 31 =
          true := by
  intro i k hk
  fin_cases i
  · exact phaseBlock017Walk00 k hk
  · exact phaseBlock017Walk01 k hk
  · exact phaseBlock017Walk02 k hk
  · exact phaseBlock017Walk03 k hk
  · exact phaseBlock017Walk04 k hk
  · exact phaseBlock017Walk05 k hk
  · exact phaseBlock017Walk06 k hk
  · exact phaseBlock017Walk07 k hk
  · exact phaseBlock017Walk08 k hk
  · exact phaseBlock017Walk09 k hk
  · exact phaseBlock017Walk10 k hk
  · exact phaseBlock017Walk11 k hk
  · exact phaseBlock017Walk12 k hk
  · exact phaseBlock017Walk13 k hk
  · exact phaseBlock017Walk14 k hk
  · exact phaseBlock017Walk15 k hk
  · exact phaseBlock017Walk16 k hk
  · exact phaseBlock017Walk17 k hk
  · exact phaseBlock017Walk18 k hk
  · exact phaseBlock017Walk19 k hk
  · exact phaseBlock017Walk20 k hk
  · exact phaseBlock017Walk21 k hk
  · exact phaseBlock017Walk22 k hk
  · exact phaseBlock017Walk23 k hk
  · exact phaseBlock017Walk24 k hk
  · exact phaseBlock017Walk25 k hk
  · exact phaseBlock017Walk26 k hk
  · exact phaseBlock017Walk27 k hk
  · exact phaseBlock017Walk28 k hk

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
