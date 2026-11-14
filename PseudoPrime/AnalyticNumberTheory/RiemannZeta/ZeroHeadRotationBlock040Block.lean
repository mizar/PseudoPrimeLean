/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock040Data
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiRotationGridRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadOrdinate1381
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock040Walk00
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock040Walk01
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock040Walk02
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock040Walk03

/-! # Block040 phase-certificate block -/

set_option linter.privateModule false

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- All 145 sequential walks pass the block 40 logarithmic block. -/
private theorem phaseBlock040Block_walks :
    ∀ (i : Fin 29) (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (9227 / 500)
            (phase1381Lower i + (k : ℚ) * (phase1381Upper i - phase1381Lower i) / 4)
            (fun j ↦ phaseBlock040BlockLower j i) (fun j ↦ phaseBlock040BlockUpper j i) 31 =
          true := by
  intro i k hk
  fin_cases i
  · exact phaseBlock040Walk00 k hk
  · exact phaseBlock040Walk01 k hk
  · exact phaseBlock040Walk02 k hk
  · exact phaseBlock040Walk03 k hk
  · exact phaseBlock040Walk04 k hk
  · exact phaseBlock040Walk05 k hk
  · exact phaseBlock040Walk06 k hk
  · exact phaseBlock040Walk07 k hk
  · exact phaseBlock040Walk08 k hk
  · exact phaseBlock040Walk09 k hk
  · exact phaseBlock040Walk10 k hk
  · exact phaseBlock040Walk11 k hk
  · exact phaseBlock040Walk12 k hk
  · exact phaseBlock040Walk13 k hk
  · exact phaseBlock040Walk14 k hk
  · exact phaseBlock040Walk15 k hk
  · exact phaseBlock040Walk16 k hk
  · exact phaseBlock040Walk17 k hk
  · exact phaseBlock040Walk18 k hk
  · exact phaseBlock040Walk19 k hk
  · exact phaseBlock040Walk20 k hk
  · exact phaseBlock040Walk21 k hk
  · exact phaseBlock040Walk22 k hk
  · exact phaseBlock040Walk23 k hk
  · exact phaseBlock040Walk24 k hk
  · exact phaseBlock040Walk25 k hk
  · exact phaseBlock040Walk26 k hk
  · exact phaseBlock040Walk27 k hk
  · exact phaseBlock040Walk28 k hk

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
