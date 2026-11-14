/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock030Data
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiRotationGridRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadOrdinate1381
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock030Walk00
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock030Walk01
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock030Walk02
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock030Walk03

/-! # Block030 phase-certificate block -/

set_option linter.privateModule false

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- All 145 sequential walks pass the block 30 logarithmic block. -/
private theorem phaseBlock030Block_walks :
    ∀ (i : Fin 29) (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (8607 / 500)
            (phase1381Lower i + (k : ℚ) * (phase1381Upper i - phase1381Lower i) / 4)
            (fun j ↦ phaseBlock030BlockLower j i) (fun j ↦ phaseBlock030BlockUpper j i) 31 =
          true := by
  intro i k hk
  fin_cases i
  · exact phaseBlock030Walk00 k hk
  · exact phaseBlock030Walk01 k hk
  · exact phaseBlock030Walk02 k hk
  · exact phaseBlock030Walk03 k hk
  · exact phaseBlock030Walk04 k hk
  · exact phaseBlock030Walk05 k hk
  · exact phaseBlock030Walk06 k hk
  · exact phaseBlock030Walk07 k hk
  · exact phaseBlock030Walk08 k hk
  · exact phaseBlock030Walk09 k hk
  · exact phaseBlock030Walk10 k hk
  · exact phaseBlock030Walk11 k hk
  · exact phaseBlock030Walk12 k hk
  · exact phaseBlock030Walk13 k hk
  · exact phaseBlock030Walk14 k hk
  · exact phaseBlock030Walk15 k hk
  · exact phaseBlock030Walk16 k hk
  · exact phaseBlock030Walk17 k hk
  · exact phaseBlock030Walk18 k hk
  · exact phaseBlock030Walk19 k hk
  · exact phaseBlock030Walk20 k hk
  · exact phaseBlock030Walk21 k hk
  · exact phaseBlock030Walk22 k hk
  · exact phaseBlock030Walk23 k hk
  · exact phaseBlock030Walk24 k hk
  · exact phaseBlock030Walk25 k hk
  · exact phaseBlock030Walk26 k hk
  · exact phaseBlock030Walk27 k hk
  · exact phaseBlock030Walk28 k hk

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
