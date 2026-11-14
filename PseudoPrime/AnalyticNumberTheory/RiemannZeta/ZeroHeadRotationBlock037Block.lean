/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock037Data
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiRotationGridRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadOrdinate1381
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock037Walk00
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock037Walk01
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock037Walk02
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock037Walk03

/-! # Block037 phase-certificate block -/

set_option linter.privateModule false

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- All 145 sequential walks pass the block 37 logarithmic block. -/
private theorem phaseBlock037Block_walks :
    ∀ (i : Fin 29) (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (9041 / 500)
            (phase1381Lower i + (k : ℚ) * (phase1381Upper i - phase1381Lower i) / 4)
            (fun j ↦ phaseBlock037BlockLower j i) (fun j ↦ phaseBlock037BlockUpper j i) 31 =
          true := by
  intro i k hk
  fin_cases i
  · exact phaseBlock037Walk00 k hk
  · exact phaseBlock037Walk01 k hk
  · exact phaseBlock037Walk02 k hk
  · exact phaseBlock037Walk03 k hk
  · exact phaseBlock037Walk04 k hk
  · exact phaseBlock037Walk05 k hk
  · exact phaseBlock037Walk06 k hk
  · exact phaseBlock037Walk07 k hk
  · exact phaseBlock037Walk08 k hk
  · exact phaseBlock037Walk09 k hk
  · exact phaseBlock037Walk10 k hk
  · exact phaseBlock037Walk11 k hk
  · exact phaseBlock037Walk12 k hk
  · exact phaseBlock037Walk13 k hk
  · exact phaseBlock037Walk14 k hk
  · exact phaseBlock037Walk15 k hk
  · exact phaseBlock037Walk16 k hk
  · exact phaseBlock037Walk17 k hk
  · exact phaseBlock037Walk18 k hk
  · exact phaseBlock037Walk19 k hk
  · exact phaseBlock037Walk20 k hk
  · exact phaseBlock037Walk21 k hk
  · exact phaseBlock037Walk22 k hk
  · exact phaseBlock037Walk23 k hk
  · exact phaseBlock037Walk24 k hk
  · exact phaseBlock037Walk25 k hk
  · exact phaseBlock037Walk26 k hk
  · exact phaseBlock037Walk27 k hk
  · exact phaseBlock037Walk28 k hk

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
