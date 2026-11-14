/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock035Data
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiRotationGridRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadOrdinate1381
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock035Walk00
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock035Walk01
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock035Walk02
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock035Walk03

/-! # Block035 phase-certificate block -/

set_option linter.privateModule false

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- All 145 sequential walks pass the block 35 logarithmic block. -/
private theorem phaseBlock035Block_walks :
    ∀ (i : Fin 29) (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (8917 / 500)
            (phase1381Lower i + (k : ℚ) * (phase1381Upper i - phase1381Lower i) / 4)
            (fun j ↦ phaseBlock035BlockLower j i) (fun j ↦ phaseBlock035BlockUpper j i) 31 =
          true := by
  intro i k hk
  fin_cases i
  · exact phaseBlock035Walk00 k hk
  · exact phaseBlock035Walk01 k hk
  · exact phaseBlock035Walk02 k hk
  · exact phaseBlock035Walk03 k hk
  · exact phaseBlock035Walk04 k hk
  · exact phaseBlock035Walk05 k hk
  · exact phaseBlock035Walk06 k hk
  · exact phaseBlock035Walk07 k hk
  · exact phaseBlock035Walk08 k hk
  · exact phaseBlock035Walk09 k hk
  · exact phaseBlock035Walk10 k hk
  · exact phaseBlock035Walk11 k hk
  · exact phaseBlock035Walk12 k hk
  · exact phaseBlock035Walk13 k hk
  · exact phaseBlock035Walk14 k hk
  · exact phaseBlock035Walk15 k hk
  · exact phaseBlock035Walk16 k hk
  · exact phaseBlock035Walk17 k hk
  · exact phaseBlock035Walk18 k hk
  · exact phaseBlock035Walk19 k hk
  · exact phaseBlock035Walk20 k hk
  · exact phaseBlock035Walk21 k hk
  · exact phaseBlock035Walk22 k hk
  · exact phaseBlock035Walk23 k hk
  · exact phaseBlock035Walk24 k hk
  · exact phaseBlock035Walk25 k hk
  · exact phaseBlock035Walk26 k hk
  · exact phaseBlock035Walk27 k hk
  · exact phaseBlock035Walk28 k hk

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
