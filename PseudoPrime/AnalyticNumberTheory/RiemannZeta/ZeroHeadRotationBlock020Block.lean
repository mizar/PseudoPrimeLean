/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock020Data
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiRotationGridRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadOrdinate1381
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock020Walk00
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock020Walk01
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock020Walk02
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock020Walk03

/-! # Block020 phase-certificate block -/

set_option linter.privateModule false

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- All 145 sequential walks pass the block 20 logarithmic block. -/
private theorem phaseBlock020Block_walks :
    ∀ (i : Fin 29) (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (7987 / 500)
            (phase1381Lower i + (k : ℚ) * (phase1381Upper i - phase1381Lower i) / 4)
            (fun j ↦ phaseBlock020BlockLower j i) (fun j ↦ phaseBlock020BlockUpper j i) 31 =
          true := by
  intro i k hk
  fin_cases i
  · exact phaseBlock020Walk00 k hk
  · exact phaseBlock020Walk01 k hk
  · exact phaseBlock020Walk02 k hk
  · exact phaseBlock020Walk03 k hk
  · exact phaseBlock020Walk04 k hk
  · exact phaseBlock020Walk05 k hk
  · exact phaseBlock020Walk06 k hk
  · exact phaseBlock020Walk07 k hk
  · exact phaseBlock020Walk08 k hk
  · exact phaseBlock020Walk09 k hk
  · exact phaseBlock020Walk10 k hk
  · exact phaseBlock020Walk11 k hk
  · exact phaseBlock020Walk12 k hk
  · exact phaseBlock020Walk13 k hk
  · exact phaseBlock020Walk14 k hk
  · exact phaseBlock020Walk15 k hk
  · exact phaseBlock020Walk16 k hk
  · exact phaseBlock020Walk17 k hk
  · exact phaseBlock020Walk18 k hk
  · exact phaseBlock020Walk19 k hk
  · exact phaseBlock020Walk20 k hk
  · exact phaseBlock020Walk21 k hk
  · exact phaseBlock020Walk22 k hk
  · exact phaseBlock020Walk23 k hk
  · exact phaseBlock020Walk24 k hk
  · exact phaseBlock020Walk25 k hk
  · exact phaseBlock020Walk26 k hk
  · exact phaseBlock020Walk27 k hk
  · exact phaseBlock020Walk28 k hk

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
