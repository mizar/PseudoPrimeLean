/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock019Data
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiRotationGridRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadOrdinate1381
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock019Walk00
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock019Walk01
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock019Walk02
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock019Walk03

/-! # Block019 phase-certificate block -/

set_option linter.privateModule false

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- All 145 sequential walks pass the block 19 logarithmic block. -/
private theorem phaseBlock019Block_walks :
    ∀ (i : Fin 29) (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (7925 / 500)
            (phase1381Lower i + (k : ℚ) * (phase1381Upper i - phase1381Lower i) / 4)
            (fun j ↦ phaseBlock019BlockLower j i) (fun j ↦ phaseBlock019BlockUpper j i) 31 =
          true := by
  intro i k hk
  fin_cases i
  · exact phaseBlock019Walk00 k hk
  · exact phaseBlock019Walk01 k hk
  · exact phaseBlock019Walk02 k hk
  · exact phaseBlock019Walk03 k hk
  · exact phaseBlock019Walk04 k hk
  · exact phaseBlock019Walk05 k hk
  · exact phaseBlock019Walk06 k hk
  · exact phaseBlock019Walk07 k hk
  · exact phaseBlock019Walk08 k hk
  · exact phaseBlock019Walk09 k hk
  · exact phaseBlock019Walk10 k hk
  · exact phaseBlock019Walk11 k hk
  · exact phaseBlock019Walk12 k hk
  · exact phaseBlock019Walk13 k hk
  · exact phaseBlock019Walk14 k hk
  · exact phaseBlock019Walk15 k hk
  · exact phaseBlock019Walk16 k hk
  · exact phaseBlock019Walk17 k hk
  · exact phaseBlock019Walk18 k hk
  · exact phaseBlock019Walk19 k hk
  · exact phaseBlock019Walk20 k hk
  · exact phaseBlock019Walk21 k hk
  · exact phaseBlock019Walk22 k hk
  · exact phaseBlock019Walk23 k hk
  · exact phaseBlock019Walk24 k hk
  · exact phaseBlock019Walk25 k hk
  · exact phaseBlock019Walk26 k hk
  · exact phaseBlock019Walk27 k hk
  · exact phaseBlock019Walk28 k hk

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
