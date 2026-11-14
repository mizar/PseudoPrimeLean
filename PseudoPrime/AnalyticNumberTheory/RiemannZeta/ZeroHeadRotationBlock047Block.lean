/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock047Data
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiRotationGridRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadOrdinate1381
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock047Walk00
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock047Walk01
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock047Walk02
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock047Walk03

/-! # Block047 phase-certificate block -/

set_option linter.privateModule false

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- All 145 sequential walks pass the block 47 logarithmic block. -/
private theorem phaseBlock047Block_walks :
    ∀ (i : Fin 29) (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (9661 / 500)
            (phase1381Lower i + (k : ℚ) * (phase1381Upper i - phase1381Lower i) / 4)
            (fun j ↦ phaseBlock047BlockLower j i) (fun j ↦ phaseBlock047BlockUpper j i) 31 =
          true := by
  intro i k hk
  fin_cases i
  · exact phaseBlock047Walk00 k hk
  · exact phaseBlock047Walk01 k hk
  · exact phaseBlock047Walk02 k hk
  · exact phaseBlock047Walk03 k hk
  · exact phaseBlock047Walk04 k hk
  · exact phaseBlock047Walk05 k hk
  · exact phaseBlock047Walk06 k hk
  · exact phaseBlock047Walk07 k hk
  · exact phaseBlock047Walk08 k hk
  · exact phaseBlock047Walk09 k hk
  · exact phaseBlock047Walk10 k hk
  · exact phaseBlock047Walk11 k hk
  · exact phaseBlock047Walk12 k hk
  · exact phaseBlock047Walk13 k hk
  · exact phaseBlock047Walk14 k hk
  · exact phaseBlock047Walk15 k hk
  · exact phaseBlock047Walk16 k hk
  · exact phaseBlock047Walk17 k hk
  · exact phaseBlock047Walk18 k hk
  · exact phaseBlock047Walk19 k hk
  · exact phaseBlock047Walk20 k hk
  · exact phaseBlock047Walk21 k hk
  · exact phaseBlock047Walk22 k hk
  · exact phaseBlock047Walk23 k hk
  · exact phaseBlock047Walk24 k hk
  · exact phaseBlock047Walk25 k hk
  · exact phaseBlock047Walk26 k hk
  · exact phaseBlock047Walk27 k hk
  · exact phaseBlock047Walk28 k hk

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
