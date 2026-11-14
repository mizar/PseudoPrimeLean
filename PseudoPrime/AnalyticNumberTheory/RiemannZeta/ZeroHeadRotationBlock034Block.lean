/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock034Data
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiRotationGridRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadOrdinate1381
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock034Walk00
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock034Walk01
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock034Walk02
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock034Walk03

/-! # Block034 phase-certificate block -/

set_option linter.privateModule false

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- All 145 sequential walks pass the block 34 logarithmic block. -/
private theorem phaseBlock034Block_walks :
    ∀ (i : Fin 29) (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (8855 / 500)
            (phase1381Lower i + (k : ℚ) * (phase1381Upper i - phase1381Lower i) / 4)
            (fun j ↦ phaseBlock034BlockLower j i) (fun j ↦ phaseBlock034BlockUpper j i) 31 =
          true := by
  intro i k hk
  fin_cases i
  · exact phaseBlock034Walk00 k hk
  · exact phaseBlock034Walk01 k hk
  · exact phaseBlock034Walk02 k hk
  · exact phaseBlock034Walk03 k hk
  · exact phaseBlock034Walk04 k hk
  · exact phaseBlock034Walk05 k hk
  · exact phaseBlock034Walk06 k hk
  · exact phaseBlock034Walk07 k hk
  · exact phaseBlock034Walk08 k hk
  · exact phaseBlock034Walk09 k hk
  · exact phaseBlock034Walk10 k hk
  · exact phaseBlock034Walk11 k hk
  · exact phaseBlock034Walk12 k hk
  · exact phaseBlock034Walk13 k hk
  · exact phaseBlock034Walk14 k hk
  · exact phaseBlock034Walk15 k hk
  · exact phaseBlock034Walk16 k hk
  · exact phaseBlock034Walk17 k hk
  · exact phaseBlock034Walk18 k hk
  · exact phaseBlock034Walk19 k hk
  · exact phaseBlock034Walk20 k hk
  · exact phaseBlock034Walk21 k hk
  · exact phaseBlock034Walk22 k hk
  · exact phaseBlock034Walk23 k hk
  · exact phaseBlock034Walk24 k hk
  · exact phaseBlock034Walk25 k hk
  · exact phaseBlock034Walk26 k hk
  · exact phaseBlock034Walk27 k hk
  · exact phaseBlock034Walk28 k hk

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
