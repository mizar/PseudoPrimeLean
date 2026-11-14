/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock051Data
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiRotationGridRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadOrdinate1381
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock051Walk00
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock051Walk01
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock051Walk02
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock051Walk03

/-! # Block051 phase-certificate block -/

set_option linter.privateModule false

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- All 145 sequential walks pass the block 51 logarithmic block. -/
private theorem phaseBlock051Block_walks :
    ∀ (i : Fin 29) (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (9909 / 500)
            (phase1381Lower i + (k : ℚ) * (phase1381Upper i - phase1381Lower i) / 4)
            (fun j ↦ phaseBlock051BlockLower j i) (fun j ↦ phaseBlock051BlockUpper j i) 31 =
          true := by
  intro i k hk
  fin_cases i
  · exact phaseBlock051Walk00 k hk
  · exact phaseBlock051Walk01 k hk
  · exact phaseBlock051Walk02 k hk
  · exact phaseBlock051Walk03 k hk
  · exact phaseBlock051Walk04 k hk
  · exact phaseBlock051Walk05 k hk
  · exact phaseBlock051Walk06 k hk
  · exact phaseBlock051Walk07 k hk
  · exact phaseBlock051Walk08 k hk
  · exact phaseBlock051Walk09 k hk
  · exact phaseBlock051Walk10 k hk
  · exact phaseBlock051Walk11 k hk
  · exact phaseBlock051Walk12 k hk
  · exact phaseBlock051Walk13 k hk
  · exact phaseBlock051Walk14 k hk
  · exact phaseBlock051Walk15 k hk
  · exact phaseBlock051Walk16 k hk
  · exact phaseBlock051Walk17 k hk
  · exact phaseBlock051Walk18 k hk
  · exact phaseBlock051Walk19 k hk
  · exact phaseBlock051Walk20 k hk
  · exact phaseBlock051Walk21 k hk
  · exact phaseBlock051Walk22 k hk
  · exact phaseBlock051Walk23 k hk
  · exact phaseBlock051Walk24 k hk
  · exact phaseBlock051Walk25 k hk
  · exact phaseBlock051Walk26 k hk
  · exact phaseBlock051Walk27 k hk
  · exact phaseBlock051Walk28 k hk

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
