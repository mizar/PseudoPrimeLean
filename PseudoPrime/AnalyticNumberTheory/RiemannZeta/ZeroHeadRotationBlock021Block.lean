/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock021Data
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiRotationGridRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadOrdinate1381
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock021Walk00
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock021Walk01
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock021Walk02
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock021Walk03

/-! # Block021 phase-certificate block -/

set_option linter.privateModule false

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- All 145 sequential walks pass the block 21 logarithmic block. -/
private theorem phaseBlock021Block_walks :
    ∀ (i : Fin 29) (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (8049 / 500)
            (phase1381Lower i + (k : ℚ) * (phase1381Upper i - phase1381Lower i) / 4)
            (fun j ↦ phaseBlock021BlockLower j i) (fun j ↦ phaseBlock021BlockUpper j i) 31 =
          true := by
  intro i k hk
  fin_cases i
  · exact phaseBlock021Walk00 k hk
  · exact phaseBlock021Walk01 k hk
  · exact phaseBlock021Walk02 k hk
  · exact phaseBlock021Walk03 k hk
  · exact phaseBlock021Walk04 k hk
  · exact phaseBlock021Walk05 k hk
  · exact phaseBlock021Walk06 k hk
  · exact phaseBlock021Walk07 k hk
  · exact phaseBlock021Walk08 k hk
  · exact phaseBlock021Walk09 k hk
  · exact phaseBlock021Walk10 k hk
  · exact phaseBlock021Walk11 k hk
  · exact phaseBlock021Walk12 k hk
  · exact phaseBlock021Walk13 k hk
  · exact phaseBlock021Walk14 k hk
  · exact phaseBlock021Walk15 k hk
  · exact phaseBlock021Walk16 k hk
  · exact phaseBlock021Walk17 k hk
  · exact phaseBlock021Walk18 k hk
  · exact phaseBlock021Walk19 k hk
  · exact phaseBlock021Walk20 k hk
  · exact phaseBlock021Walk21 k hk
  · exact phaseBlock021Walk22 k hk
  · exact phaseBlock021Walk23 k hk
  · exact phaseBlock021Walk24 k hk
  · exact phaseBlock021Walk25 k hk
  · exact phaseBlock021Walk26 k hk
  · exact phaseBlock021Walk27 k hk
  · exact phaseBlock021Walk28 k hk

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
