/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock052Data
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiRotationGridRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadOrdinate1381
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock052Walk00
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock052Walk01
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock052Walk02
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock052Walk03

/-! # Block052 phase-certificate block -/

set_option linter.privateModule false

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- All 145 sequential walks pass the block 52 logarithmic block. -/
private theorem phaseBlock052Block_walks :
    ∀ (i : Fin 29) (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (9971 / 500)
            (phase1381Lower i + (k : ℚ) * (phase1381Upper i - phase1381Lower i) / 4)
            (fun j ↦ phaseBlock052BlockLower j i) (fun j ↦ phaseBlock052BlockUpper j i) 31 =
          true := by
  intro i k hk
  fin_cases i
  · exact phaseBlock052Walk00 k hk
  · exact phaseBlock052Walk01 k hk
  · exact phaseBlock052Walk02 k hk
  · exact phaseBlock052Walk03 k hk
  · exact phaseBlock052Walk04 k hk
  · exact phaseBlock052Walk05 k hk
  · exact phaseBlock052Walk06 k hk
  · exact phaseBlock052Walk07 k hk
  · exact phaseBlock052Walk08 k hk
  · exact phaseBlock052Walk09 k hk
  · exact phaseBlock052Walk10 k hk
  · exact phaseBlock052Walk11 k hk
  · exact phaseBlock052Walk12 k hk
  · exact phaseBlock052Walk13 k hk
  · exact phaseBlock052Walk14 k hk
  · exact phaseBlock052Walk15 k hk
  · exact phaseBlock052Walk16 k hk
  · exact phaseBlock052Walk17 k hk
  · exact phaseBlock052Walk18 k hk
  · exact phaseBlock052Walk19 k hk
  · exact phaseBlock052Walk20 k hk
  · exact phaseBlock052Walk21 k hk
  · exact phaseBlock052Walk22 k hk
  · exact phaseBlock052Walk23 k hk
  · exact phaseBlock052Walk24 k hk
  · exact phaseBlock052Walk25 k hk
  · exact phaseBlock052Walk26 k hk
  · exact phaseBlock052Walk27 k hk
  · exact phaseBlock052Walk28 k hk

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
