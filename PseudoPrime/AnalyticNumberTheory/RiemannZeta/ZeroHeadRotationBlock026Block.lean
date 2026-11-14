/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock026Data
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiRotationGridRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadOrdinate1381
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock026Walk00
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock026Walk01
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock026Walk02
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock026Walk03

/-! # Block026 phase-certificate block -/

set_option linter.privateModule false

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- All 145 sequential walks pass the block 26 logarithmic block. -/
private theorem phaseBlock026Block_walks :
    ∀ (i : Fin 29) (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (8359 / 500)
            (phase1381Lower i + (k : ℚ) * (phase1381Upper i - phase1381Lower i) / 4)
            (fun j ↦ phaseBlock026BlockLower j i) (fun j ↦ phaseBlock026BlockUpper j i) 31 =
          true := by
  intro i k hk
  fin_cases i
  · exact phaseBlock026Walk00 k hk
  · exact phaseBlock026Walk01 k hk
  · exact phaseBlock026Walk02 k hk
  · exact phaseBlock026Walk03 k hk
  · exact phaseBlock026Walk04 k hk
  · exact phaseBlock026Walk05 k hk
  · exact phaseBlock026Walk06 k hk
  · exact phaseBlock026Walk07 k hk
  · exact phaseBlock026Walk08 k hk
  · exact phaseBlock026Walk09 k hk
  · exact phaseBlock026Walk10 k hk
  · exact phaseBlock026Walk11 k hk
  · exact phaseBlock026Walk12 k hk
  · exact phaseBlock026Walk13 k hk
  · exact phaseBlock026Walk14 k hk
  · exact phaseBlock026Walk15 k hk
  · exact phaseBlock026Walk16 k hk
  · exact phaseBlock026Walk17 k hk
  · exact phaseBlock026Walk18 k hk
  · exact phaseBlock026Walk19 k hk
  · exact phaseBlock026Walk20 k hk
  · exact phaseBlock026Walk21 k hk
  · exact phaseBlock026Walk22 k hk
  · exact phaseBlock026Walk23 k hk
  · exact phaseBlock026Walk24 k hk
  · exact phaseBlock026Walk25 k hk
  · exact phaseBlock026Walk26 k hk
  · exact phaseBlock026Walk27 k hk
  · exact phaseBlock026Walk28 k hk

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
