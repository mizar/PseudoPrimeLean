/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock029Data
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiRotationGridRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadOrdinate1381
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock029Walk00
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock029Walk01
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock029Walk02
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock029Walk03

/-! # Block029 phase-certificate block -/

set_option linter.privateModule false

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- All 145 sequential walks pass the block 29 logarithmic block. -/
private theorem phaseBlock029Block_walks :
    ∀ (i : Fin 29) (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (8545 / 500)
            (phase1381Lower i + (k : ℚ) * (phase1381Upper i - phase1381Lower i) / 4)
            (fun j ↦ phaseBlock029BlockLower j i) (fun j ↦ phaseBlock029BlockUpper j i) 31 =
          true := by
  intro i k hk
  fin_cases i
  · exact phaseBlock029Walk00 k hk
  · exact phaseBlock029Walk01 k hk
  · exact phaseBlock029Walk02 k hk
  · exact phaseBlock029Walk03 k hk
  · exact phaseBlock029Walk04 k hk
  · exact phaseBlock029Walk05 k hk
  · exact phaseBlock029Walk06 k hk
  · exact phaseBlock029Walk07 k hk
  · exact phaseBlock029Walk08 k hk
  · exact phaseBlock029Walk09 k hk
  · exact phaseBlock029Walk10 k hk
  · exact phaseBlock029Walk11 k hk
  · exact phaseBlock029Walk12 k hk
  · exact phaseBlock029Walk13 k hk
  · exact phaseBlock029Walk14 k hk
  · exact phaseBlock029Walk15 k hk
  · exact phaseBlock029Walk16 k hk
  · exact phaseBlock029Walk17 k hk
  · exact phaseBlock029Walk18 k hk
  · exact phaseBlock029Walk19 k hk
  · exact phaseBlock029Walk20 k hk
  · exact phaseBlock029Walk21 k hk
  · exact phaseBlock029Walk22 k hk
  · exact phaseBlock029Walk23 k hk
  · exact phaseBlock029Walk24 k hk
  · exact phaseBlock029Walk25 k hk
  · exact phaseBlock029Walk26 k hk
  · exact phaseBlock029Walk27 k hk
  · exact phaseBlock029Walk28 k hk

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
