/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock048Data
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiRotationGridRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadOrdinate1381
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock048Walk00
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock048Walk01
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock048Walk02
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock048Walk03

/-! # Block048 phase-certificate block -/

set_option linter.privateModule false

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- All 145 sequential walks pass the block 48 logarithmic block. -/
private theorem phaseBlock048Block_walks :
    ∀ (i : Fin 29) (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (9723 / 500)
            (phase1381Lower i + (k : ℚ) * (phase1381Upper i - phase1381Lower i) / 4)
            (fun j ↦ phaseBlock048BlockLower j i) (fun j ↦ phaseBlock048BlockUpper j i) 31 =
          true := by
  intro i k hk
  fin_cases i
  · exact phaseBlock048Walk00 k hk
  · exact phaseBlock048Walk01 k hk
  · exact phaseBlock048Walk02 k hk
  · exact phaseBlock048Walk03 k hk
  · exact phaseBlock048Walk04 k hk
  · exact phaseBlock048Walk05 k hk
  · exact phaseBlock048Walk06 k hk
  · exact phaseBlock048Walk07 k hk
  · exact phaseBlock048Walk08 k hk
  · exact phaseBlock048Walk09 k hk
  · exact phaseBlock048Walk10 k hk
  · exact phaseBlock048Walk11 k hk
  · exact phaseBlock048Walk12 k hk
  · exact phaseBlock048Walk13 k hk
  · exact phaseBlock048Walk14 k hk
  · exact phaseBlock048Walk15 k hk
  · exact phaseBlock048Walk16 k hk
  · exact phaseBlock048Walk17 k hk
  · exact phaseBlock048Walk18 k hk
  · exact phaseBlock048Walk19 k hk
  · exact phaseBlock048Walk20 k hk
  · exact phaseBlock048Walk21 k hk
  · exact phaseBlock048Walk22 k hk
  · exact phaseBlock048Walk23 k hk
  · exact phaseBlock048Walk24 k hk
  · exact phaseBlock048Walk25 k hk
  · exact phaseBlock048Walk26 k hk
  · exact phaseBlock048Walk27 k hk
  · exact phaseBlock048Walk28 k hk

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
