/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock045Data
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiRotationGridRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadOrdinate1381
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock045Walk00
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock045Walk01
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock045Walk02
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock045Walk03

/-! # Block045 phase-certificate block -/

set_option linter.privateModule false

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- All 145 sequential walks pass the block 45 logarithmic block. -/
private theorem phaseBlock045Block_walks :
    ∀ (i : Fin 29) (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (9537 / 500)
            (phase1381Lower i + (k : ℚ) * (phase1381Upper i - phase1381Lower i) / 4)
            (fun j ↦ phaseBlock045BlockLower j i) (fun j ↦ phaseBlock045BlockUpper j i) 31 =
          true := by
  intro i k hk
  fin_cases i
  · exact phaseBlock045Walk00 k hk
  · exact phaseBlock045Walk01 k hk
  · exact phaseBlock045Walk02 k hk
  · exact phaseBlock045Walk03 k hk
  · exact phaseBlock045Walk04 k hk
  · exact phaseBlock045Walk05 k hk
  · exact phaseBlock045Walk06 k hk
  · exact phaseBlock045Walk07 k hk
  · exact phaseBlock045Walk08 k hk
  · exact phaseBlock045Walk09 k hk
  · exact phaseBlock045Walk10 k hk
  · exact phaseBlock045Walk11 k hk
  · exact phaseBlock045Walk12 k hk
  · exact phaseBlock045Walk13 k hk
  · exact phaseBlock045Walk14 k hk
  · exact phaseBlock045Walk15 k hk
  · exact phaseBlock045Walk16 k hk
  · exact phaseBlock045Walk17 k hk
  · exact phaseBlock045Walk18 k hk
  · exact phaseBlock045Walk19 k hk
  · exact phaseBlock045Walk20 k hk
  · exact phaseBlock045Walk21 k hk
  · exact phaseBlock045Walk22 k hk
  · exact phaseBlock045Walk23 k hk
  · exact phaseBlock045Walk24 k hk
  · exact phaseBlock045Walk25 k hk
  · exact phaseBlock045Walk26 k hk
  · exact phaseBlock045Walk27 k hk
  · exact phaseBlock045Walk28 k hk

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
