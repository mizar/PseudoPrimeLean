/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock036Data
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiRotationGridRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadOrdinate1381
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock036Walk00
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock036Walk01
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock036Walk02
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock036Walk03

/-! # Block036 phase-certificate block -/

set_option linter.privateModule false

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- All 145 sequential walks pass the block 36 logarithmic block. -/
private theorem phaseBlock036Block_walks :
    ∀ (i : Fin 29) (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (8979 / 500)
            (phase1381Lower i + (k : ℚ) * (phase1381Upper i - phase1381Lower i) / 4)
            (fun j ↦ phaseBlock036BlockLower j i) (fun j ↦ phaseBlock036BlockUpper j i) 31 =
          true := by
  intro i k hk
  fin_cases i
  · exact phaseBlock036Walk00 k hk
  · exact phaseBlock036Walk01 k hk
  · exact phaseBlock036Walk02 k hk
  · exact phaseBlock036Walk03 k hk
  · exact phaseBlock036Walk04 k hk
  · exact phaseBlock036Walk05 k hk
  · exact phaseBlock036Walk06 k hk
  · exact phaseBlock036Walk07 k hk
  · exact phaseBlock036Walk08 k hk
  · exact phaseBlock036Walk09 k hk
  · exact phaseBlock036Walk10 k hk
  · exact phaseBlock036Walk11 k hk
  · exact phaseBlock036Walk12 k hk
  · exact phaseBlock036Walk13 k hk
  · exact phaseBlock036Walk14 k hk
  · exact phaseBlock036Walk15 k hk
  · exact phaseBlock036Walk16 k hk
  · exact phaseBlock036Walk17 k hk
  · exact phaseBlock036Walk18 k hk
  · exact phaseBlock036Walk19 k hk
  · exact phaseBlock036Walk20 k hk
  · exact phaseBlock036Walk21 k hk
  · exact phaseBlock036Walk22 k hk
  · exact phaseBlock036Walk23 k hk
  · exact phaseBlock036Walk24 k hk
  · exact phaseBlock036Walk25 k hk
  · exact phaseBlock036Walk26 k hk
  · exact phaseBlock036Walk27 k hk
  · exact phaseBlock036Walk28 k hk

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
