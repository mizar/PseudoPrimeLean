/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock049Data
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiRotationGridRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadOrdinate1381
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock049Walk00
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock049Walk01
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock049Walk02
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock049Walk03

/-! # Block049 phase-certificate block -/

set_option linter.privateModule false

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- All 145 sequential walks pass the block 49 logarithmic block. -/
private theorem phaseBlock049Block_walks :
    ∀ (i : Fin 29) (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (9785 / 500)
            (phase1381Lower i + (k : ℚ) * (phase1381Upper i - phase1381Lower i) / 4)
            (fun j ↦ phaseBlock049BlockLower j i) (fun j ↦ phaseBlock049BlockUpper j i) 31 =
          true := by
  intro i k hk
  fin_cases i
  · exact phaseBlock049Walk00 k hk
  · exact phaseBlock049Walk01 k hk
  · exact phaseBlock049Walk02 k hk
  · exact phaseBlock049Walk03 k hk
  · exact phaseBlock049Walk04 k hk
  · exact phaseBlock049Walk05 k hk
  · exact phaseBlock049Walk06 k hk
  · exact phaseBlock049Walk07 k hk
  · exact phaseBlock049Walk08 k hk
  · exact phaseBlock049Walk09 k hk
  · exact phaseBlock049Walk10 k hk
  · exact phaseBlock049Walk11 k hk
  · exact phaseBlock049Walk12 k hk
  · exact phaseBlock049Walk13 k hk
  · exact phaseBlock049Walk14 k hk
  · exact phaseBlock049Walk15 k hk
  · exact phaseBlock049Walk16 k hk
  · exact phaseBlock049Walk17 k hk
  · exact phaseBlock049Walk18 k hk
  · exact phaseBlock049Walk19 k hk
  · exact phaseBlock049Walk20 k hk
  · exact phaseBlock049Walk21 k hk
  · exact phaseBlock049Walk22 k hk
  · exact phaseBlock049Walk23 k hk
  · exact phaseBlock049Walk24 k hk
  · exact phaseBlock049Walk25 k hk
  · exact phaseBlock049Walk26 k hk
  · exact phaseBlock049Walk27 k hk
  · exact phaseBlock049Walk28 k hk

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
