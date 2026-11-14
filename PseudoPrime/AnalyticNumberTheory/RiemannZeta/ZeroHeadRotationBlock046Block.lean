/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock046Data
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiRotationGridRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadOrdinate1381
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock046Walk00
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock046Walk01
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock046Walk02
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock046Walk03

/-! # Block046 phase-certificate block -/

set_option linter.privateModule false

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- All 145 sequential walks pass the block 46 logarithmic block. -/
private theorem phaseBlock046Block_walks :
    ∀ (i : Fin 29) (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (9599 / 500)
            (phase1381Lower i + (k : ℚ) * (phase1381Upper i - phase1381Lower i) / 4)
            (fun j ↦ phaseBlock046BlockLower j i) (fun j ↦ phaseBlock046BlockUpper j i) 31 =
          true := by
  intro i k hk
  fin_cases i
  · exact phaseBlock046Walk00 k hk
  · exact phaseBlock046Walk01 k hk
  · exact phaseBlock046Walk02 k hk
  · exact phaseBlock046Walk03 k hk
  · exact phaseBlock046Walk04 k hk
  · exact phaseBlock046Walk05 k hk
  · exact phaseBlock046Walk06 k hk
  · exact phaseBlock046Walk07 k hk
  · exact phaseBlock046Walk08 k hk
  · exact phaseBlock046Walk09 k hk
  · exact phaseBlock046Walk10 k hk
  · exact phaseBlock046Walk11 k hk
  · exact phaseBlock046Walk12 k hk
  · exact phaseBlock046Walk13 k hk
  · exact phaseBlock046Walk14 k hk
  · exact phaseBlock046Walk15 k hk
  · exact phaseBlock046Walk16 k hk
  · exact phaseBlock046Walk17 k hk
  · exact phaseBlock046Walk18 k hk
  · exact phaseBlock046Walk19 k hk
  · exact phaseBlock046Walk20 k hk
  · exact phaseBlock046Walk21 k hk
  · exact phaseBlock046Walk22 k hk
  · exact phaseBlock046Walk23 k hk
  · exact phaseBlock046Walk24 k hk
  · exact phaseBlock046Walk25 k hk
  · exact phaseBlock046Walk26 k hk
  · exact phaseBlock046Walk27 k hk
  · exact phaseBlock046Walk28 k hk

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
