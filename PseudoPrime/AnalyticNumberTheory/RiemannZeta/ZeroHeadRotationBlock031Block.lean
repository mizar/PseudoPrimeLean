/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock031Data
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiRotationGridRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadOrdinate1381
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock031Walk00
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock031Walk01
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock031Walk02
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock031Walk03

/-! # Block031 phase-certificate block -/

set_option linter.privateModule false

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- All 145 sequential walks pass the block 31 logarithmic block. -/
private theorem phaseBlock031Block_walks :
    ∀ (i : Fin 29) (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (8669 / 500)
            (phase1381Lower i + (k : ℚ) * (phase1381Upper i - phase1381Lower i) / 4)
            (fun j ↦ phaseBlock031BlockLower j i) (fun j ↦ phaseBlock031BlockUpper j i) 31 =
          true := by
  intro i k hk
  fin_cases i
  · exact phaseBlock031Walk00 k hk
  · exact phaseBlock031Walk01 k hk
  · exact phaseBlock031Walk02 k hk
  · exact phaseBlock031Walk03 k hk
  · exact phaseBlock031Walk04 k hk
  · exact phaseBlock031Walk05 k hk
  · exact phaseBlock031Walk06 k hk
  · exact phaseBlock031Walk07 k hk
  · exact phaseBlock031Walk08 k hk
  · exact phaseBlock031Walk09 k hk
  · exact phaseBlock031Walk10 k hk
  · exact phaseBlock031Walk11 k hk
  · exact phaseBlock031Walk12 k hk
  · exact phaseBlock031Walk13 k hk
  · exact phaseBlock031Walk14 k hk
  · exact phaseBlock031Walk15 k hk
  · exact phaseBlock031Walk16 k hk
  · exact phaseBlock031Walk17 k hk
  · exact phaseBlock031Walk18 k hk
  · exact phaseBlock031Walk19 k hk
  · exact phaseBlock031Walk20 k hk
  · exact phaseBlock031Walk21 k hk
  · exact phaseBlock031Walk22 k hk
  · exact phaseBlock031Walk23 k hk
  · exact phaseBlock031Walk24 k hk
  · exact phaseBlock031Walk25 k hk
  · exact phaseBlock031Walk26 k hk
  · exact phaseBlock031Walk27 k hk
  · exact phaseBlock031Walk28 k hk

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
