/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock039Data
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiRotationGridRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadOrdinate1381
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock039Walk00
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock039Walk01
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock039Walk02
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock039Walk03

/-! # Block039 phase-certificate block -/

set_option linter.privateModule false

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- All 145 sequential walks pass the block 39 logarithmic block. -/
private theorem phaseBlock039Block_walks :
    ∀ (i : Fin 29) (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (9165 / 500)
            (phase1381Lower i + (k : ℚ) * (phase1381Upper i - phase1381Lower i) / 4)
            (fun j ↦ phaseBlock039BlockLower j i) (fun j ↦ phaseBlock039BlockUpper j i) 31 =
          true := by
  intro i k hk
  fin_cases i
  · exact phaseBlock039Walk00 k hk
  · exact phaseBlock039Walk01 k hk
  · exact phaseBlock039Walk02 k hk
  · exact phaseBlock039Walk03 k hk
  · exact phaseBlock039Walk04 k hk
  · exact phaseBlock039Walk05 k hk
  · exact phaseBlock039Walk06 k hk
  · exact phaseBlock039Walk07 k hk
  · exact phaseBlock039Walk08 k hk
  · exact phaseBlock039Walk09 k hk
  · exact phaseBlock039Walk10 k hk
  · exact phaseBlock039Walk11 k hk
  · exact phaseBlock039Walk12 k hk
  · exact phaseBlock039Walk13 k hk
  · exact phaseBlock039Walk14 k hk
  · exact phaseBlock039Walk15 k hk
  · exact phaseBlock039Walk16 k hk
  · exact phaseBlock039Walk17 k hk
  · exact phaseBlock039Walk18 k hk
  · exact phaseBlock039Walk19 k hk
  · exact phaseBlock039Walk20 k hk
  · exact phaseBlock039Walk21 k hk
  · exact phaseBlock039Walk22 k hk
  · exact phaseBlock039Walk23 k hk
  · exact phaseBlock039Walk24 k hk
  · exact phaseBlock039Walk25 k hk
  · exact phaseBlock039Walk26 k hk
  · exact phaseBlock039Walk27 k hk
  · exact phaseBlock039Walk28 k hk

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
