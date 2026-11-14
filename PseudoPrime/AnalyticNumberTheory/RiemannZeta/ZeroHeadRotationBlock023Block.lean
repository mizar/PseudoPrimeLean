/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock023Data
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiRotationGridRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadOrdinate1381
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock023Walk00
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock023Walk01
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock023Walk02
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock023Walk03

/-! # Block023 phase-certificate block -/

set_option linter.privateModule false

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- All 145 sequential walks pass the block 23 logarithmic block. -/
private theorem phaseBlock023Block_walks :
    ∀ (i : Fin 29) (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (8173 / 500)
            (phase1381Lower i + (k : ℚ) * (phase1381Upper i - phase1381Lower i) / 4)
            (fun j ↦ phaseBlock023BlockLower j i) (fun j ↦ phaseBlock023BlockUpper j i) 31 =
          true := by
  intro i k hk
  fin_cases i
  · exact phaseBlock023Walk00 k hk
  · exact phaseBlock023Walk01 k hk
  · exact phaseBlock023Walk02 k hk
  · exact phaseBlock023Walk03 k hk
  · exact phaseBlock023Walk04 k hk
  · exact phaseBlock023Walk05 k hk
  · exact phaseBlock023Walk06 k hk
  · exact phaseBlock023Walk07 k hk
  · exact phaseBlock023Walk08 k hk
  · exact phaseBlock023Walk09 k hk
  · exact phaseBlock023Walk10 k hk
  · exact phaseBlock023Walk11 k hk
  · exact phaseBlock023Walk12 k hk
  · exact phaseBlock023Walk13 k hk
  · exact phaseBlock023Walk14 k hk
  · exact phaseBlock023Walk15 k hk
  · exact phaseBlock023Walk16 k hk
  · exact phaseBlock023Walk17 k hk
  · exact phaseBlock023Walk18 k hk
  · exact phaseBlock023Walk19 k hk
  · exact phaseBlock023Walk20 k hk
  · exact phaseBlock023Walk21 k hk
  · exact phaseBlock023Walk22 k hk
  · exact phaseBlock023Walk23 k hk
  · exact phaseBlock023Walk24 k hk
  · exact phaseBlock023Walk25 k hk
  · exact phaseBlock023Walk26 k hk
  · exact phaseBlock023Walk27 k hk
  · exact phaseBlock023Walk28 k hk

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
