/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock022Data
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiRotationGridRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadOrdinate1381
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock022Walk00
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock022Walk01
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock022Walk02
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock022Walk03

/-! # Block022 phase-certificate block -/

set_option linter.privateModule false

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- All 145 sequential walks pass the block 22 logarithmic block. -/
private theorem phaseBlock022Block_walks :
    ∀ (i : Fin 29) (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (8111 / 500)
            (phase1381Lower i + (k : ℚ) * (phase1381Upper i - phase1381Lower i) / 4)
            (fun j ↦ phaseBlock022BlockLower j i) (fun j ↦ phaseBlock022BlockUpper j i) 31 =
          true := by
  intro i k hk
  fin_cases i
  · exact phaseBlock022Walk00 k hk
  · exact phaseBlock022Walk01 k hk
  · exact phaseBlock022Walk02 k hk
  · exact phaseBlock022Walk03 k hk
  · exact phaseBlock022Walk04 k hk
  · exact phaseBlock022Walk05 k hk
  · exact phaseBlock022Walk06 k hk
  · exact phaseBlock022Walk07 k hk
  · exact phaseBlock022Walk08 k hk
  · exact phaseBlock022Walk09 k hk
  · exact phaseBlock022Walk10 k hk
  · exact phaseBlock022Walk11 k hk
  · exact phaseBlock022Walk12 k hk
  · exact phaseBlock022Walk13 k hk
  · exact phaseBlock022Walk14 k hk
  · exact phaseBlock022Walk15 k hk
  · exact phaseBlock022Walk16 k hk
  · exact phaseBlock022Walk17 k hk
  · exact phaseBlock022Walk18 k hk
  · exact phaseBlock022Walk19 k hk
  · exact phaseBlock022Walk20 k hk
  · exact phaseBlock022Walk21 k hk
  · exact phaseBlock022Walk22 k hk
  · exact phaseBlock022Walk23 k hk
  · exact phaseBlock022Walk24 k hk
  · exact phaseBlock022Walk25 k hk
  · exact phaseBlock022Walk26 k hk
  · exact phaseBlock022Walk27 k hk
  · exact phaseBlock022Walk28 k hk

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
