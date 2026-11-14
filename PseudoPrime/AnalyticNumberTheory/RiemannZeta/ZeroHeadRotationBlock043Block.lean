/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock043Data
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiRotationGridRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadOrdinate1381
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock043Walk00
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock043Walk01
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock043Walk02
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock043Walk03

/-! # Block043 phase-certificate block -/

set_option linter.privateModule false

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- All 145 sequential walks pass the block 43 logarithmic block. -/
private theorem phaseBlock043Block_walks :
    ∀ (i : Fin 29) (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (9413 / 500)
            (phase1381Lower i + (k : ℚ) * (phase1381Upper i - phase1381Lower i) / 4)
            (fun j ↦ phaseBlock043BlockLower j i) (fun j ↦ phaseBlock043BlockUpper j i) 31 =
          true := by
  intro i k hk
  fin_cases i
  · exact phaseBlock043Walk00 k hk
  · exact phaseBlock043Walk01 k hk
  · exact phaseBlock043Walk02 k hk
  · exact phaseBlock043Walk03 k hk
  · exact phaseBlock043Walk04 k hk
  · exact phaseBlock043Walk05 k hk
  · exact phaseBlock043Walk06 k hk
  · exact phaseBlock043Walk07 k hk
  · exact phaseBlock043Walk08 k hk
  · exact phaseBlock043Walk09 k hk
  · exact phaseBlock043Walk10 k hk
  · exact phaseBlock043Walk11 k hk
  · exact phaseBlock043Walk12 k hk
  · exact phaseBlock043Walk13 k hk
  · exact phaseBlock043Walk14 k hk
  · exact phaseBlock043Walk15 k hk
  · exact phaseBlock043Walk16 k hk
  · exact phaseBlock043Walk17 k hk
  · exact phaseBlock043Walk18 k hk
  · exact phaseBlock043Walk19 k hk
  · exact phaseBlock043Walk20 k hk
  · exact phaseBlock043Walk21 k hk
  · exact phaseBlock043Walk22 k hk
  · exact phaseBlock043Walk23 k hk
  · exact phaseBlock043Walk24 k hk
  · exact phaseBlock043Walk25 k hk
  · exact phaseBlock043Walk26 k hk
  · exact phaseBlock043Walk27 k hk
  · exact phaseBlock043Walk28 k hk

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
