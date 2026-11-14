/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock032Data
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiRotationGridRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadOrdinate1381
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock032Walk00
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock032Walk01
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock032Walk02
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock032Walk03

/-! # Block032 phase-certificate block -/

set_option linter.privateModule false

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- All 145 sequential walks pass the block 32 logarithmic block. -/
private theorem phaseBlock032Block_walks :
    ∀ (i : Fin 29) (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (8731 / 500)
            (phase1381Lower i + (k : ℚ) * (phase1381Upper i - phase1381Lower i) / 4)
            (fun j ↦ phaseBlock032BlockLower j i) (fun j ↦ phaseBlock032BlockUpper j i) 31 =
          true := by
  intro i k hk
  fin_cases i
  · exact phaseBlock032Walk00 k hk
  · exact phaseBlock032Walk01 k hk
  · exact phaseBlock032Walk02 k hk
  · exact phaseBlock032Walk03 k hk
  · exact phaseBlock032Walk04 k hk
  · exact phaseBlock032Walk05 k hk
  · exact phaseBlock032Walk06 k hk
  · exact phaseBlock032Walk07 k hk
  · exact phaseBlock032Walk08 k hk
  · exact phaseBlock032Walk09 k hk
  · exact phaseBlock032Walk10 k hk
  · exact phaseBlock032Walk11 k hk
  · exact phaseBlock032Walk12 k hk
  · exact phaseBlock032Walk13 k hk
  · exact phaseBlock032Walk14 k hk
  · exact phaseBlock032Walk15 k hk
  · exact phaseBlock032Walk16 k hk
  · exact phaseBlock032Walk17 k hk
  · exact phaseBlock032Walk18 k hk
  · exact phaseBlock032Walk19 k hk
  · exact phaseBlock032Walk20 k hk
  · exact phaseBlock032Walk21 k hk
  · exact phaseBlock032Walk22 k hk
  · exact phaseBlock032Walk23 k hk
  · exact phaseBlock032Walk24 k hk
  · exact phaseBlock032Walk25 k hk
  · exact phaseBlock032Walk26 k hk
  · exact phaseBlock032Walk27 k hk
  · exact phaseBlock032Walk28 k hk

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
