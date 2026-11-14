/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock042Data
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiRotationGridRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadOrdinate1381
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock042Walk00
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock042Walk01
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock042Walk02
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock042Walk03

/-! # Block042 phase-certificate block -/

set_option linter.privateModule false

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- All 145 sequential walks pass the block 42 logarithmic block. -/
private theorem phaseBlock042Block_walks :
    ∀ (i : Fin 29) (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (9351 / 500)
            (phase1381Lower i + (k : ℚ) * (phase1381Upper i - phase1381Lower i) / 4)
            (fun j ↦ phaseBlock042BlockLower j i) (fun j ↦ phaseBlock042BlockUpper j i) 31 =
          true := by
  intro i k hk
  fin_cases i
  · exact phaseBlock042Walk00 k hk
  · exact phaseBlock042Walk01 k hk
  · exact phaseBlock042Walk02 k hk
  · exact phaseBlock042Walk03 k hk
  · exact phaseBlock042Walk04 k hk
  · exact phaseBlock042Walk05 k hk
  · exact phaseBlock042Walk06 k hk
  · exact phaseBlock042Walk07 k hk
  · exact phaseBlock042Walk08 k hk
  · exact phaseBlock042Walk09 k hk
  · exact phaseBlock042Walk10 k hk
  · exact phaseBlock042Walk11 k hk
  · exact phaseBlock042Walk12 k hk
  · exact phaseBlock042Walk13 k hk
  · exact phaseBlock042Walk14 k hk
  · exact phaseBlock042Walk15 k hk
  · exact phaseBlock042Walk16 k hk
  · exact phaseBlock042Walk17 k hk
  · exact phaseBlock042Walk18 k hk
  · exact phaseBlock042Walk19 k hk
  · exact phaseBlock042Walk20 k hk
  · exact phaseBlock042Walk21 k hk
  · exact phaseBlock042Walk22 k hk
  · exact phaseBlock042Walk23 k hk
  · exact phaseBlock042Walk24 k hk
  · exact phaseBlock042Walk25 k hk
  · exact phaseBlock042Walk26 k hk
  · exact phaseBlock042Walk27 k hk
  · exact phaseBlock042Walk28 k hk

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
