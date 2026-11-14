/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock050Data
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiRotationGridRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadOrdinate1381
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock050Walk00
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock050Walk01
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock050Walk02
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock050Walk03

/-! # Block050 phase-certificate block -/

set_option linter.privateModule false

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- All 145 sequential walks pass the block 50 logarithmic block. -/
private theorem phaseBlock050Block_walks :
    ∀ (i : Fin 29) (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (9847 / 500)
            (phase1381Lower i + (k : ℚ) * (phase1381Upper i - phase1381Lower i) / 4)
            (fun j ↦ phaseBlock050BlockLower j i) (fun j ↦ phaseBlock050BlockUpper j i) 31 =
          true := by
  intro i k hk
  fin_cases i
  · exact phaseBlock050Walk00 k hk
  · exact phaseBlock050Walk01 k hk
  · exact phaseBlock050Walk02 k hk
  · exact phaseBlock050Walk03 k hk
  · exact phaseBlock050Walk04 k hk
  · exact phaseBlock050Walk05 k hk
  · exact phaseBlock050Walk06 k hk
  · exact phaseBlock050Walk07 k hk
  · exact phaseBlock050Walk08 k hk
  · exact phaseBlock050Walk09 k hk
  · exact phaseBlock050Walk10 k hk
  · exact phaseBlock050Walk11 k hk
  · exact phaseBlock050Walk12 k hk
  · exact phaseBlock050Walk13 k hk
  · exact phaseBlock050Walk14 k hk
  · exact phaseBlock050Walk15 k hk
  · exact phaseBlock050Walk16 k hk
  · exact phaseBlock050Walk17 k hk
  · exact phaseBlock050Walk18 k hk
  · exact phaseBlock050Walk19 k hk
  · exact phaseBlock050Walk20 k hk
  · exact phaseBlock050Walk21 k hk
  · exact phaseBlock050Walk22 k hk
  · exact phaseBlock050Walk23 k hk
  · exact phaseBlock050Walk24 k hk
  · exact phaseBlock050Walk25 k hk
  · exact phaseBlock050Walk26 k hk
  · exact phaseBlock050Walk27 k hk
  · exact phaseBlock050Walk28 k hk

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
