/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock027Data
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiRotationGridRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadOrdinate1381
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock027Walk00
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock027Walk01
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock027Walk02
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock027Walk03

/-! # Block027 phase-certificate block -/

set_option linter.privateModule false

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- All 145 sequential walks pass the block 27 logarithmic block. -/
private theorem phaseBlock027Block_walks :
    ∀ (i : Fin 29) (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (8421 / 500)
            (phase1381Lower i + (k : ℚ) * (phase1381Upper i - phase1381Lower i) / 4)
            (fun j ↦ phaseBlock027BlockLower j i) (fun j ↦ phaseBlock027BlockUpper j i) 31 =
          true := by
  intro i k hk
  fin_cases i
  · exact phaseBlock027Walk00 k hk
  · exact phaseBlock027Walk01 k hk
  · exact phaseBlock027Walk02 k hk
  · exact phaseBlock027Walk03 k hk
  · exact phaseBlock027Walk04 k hk
  · exact phaseBlock027Walk05 k hk
  · exact phaseBlock027Walk06 k hk
  · exact phaseBlock027Walk07 k hk
  · exact phaseBlock027Walk08 k hk
  · exact phaseBlock027Walk09 k hk
  · exact phaseBlock027Walk10 k hk
  · exact phaseBlock027Walk11 k hk
  · exact phaseBlock027Walk12 k hk
  · exact phaseBlock027Walk13 k hk
  · exact phaseBlock027Walk14 k hk
  · exact phaseBlock027Walk15 k hk
  · exact phaseBlock027Walk16 k hk
  · exact phaseBlock027Walk17 k hk
  · exact phaseBlock027Walk18 k hk
  · exact phaseBlock027Walk19 k hk
  · exact phaseBlock027Walk20 k hk
  · exact phaseBlock027Walk21 k hk
  · exact phaseBlock027Walk22 k hk
  · exact phaseBlock027Walk23 k hk
  · exact phaseBlock027Walk24 k hk
  · exact phaseBlock027Walk25 k hk
  · exact phaseBlock027Walk26 k hk
  · exact phaseBlock027Walk27 k hk
  · exact phaseBlock027Walk28 k hk

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
