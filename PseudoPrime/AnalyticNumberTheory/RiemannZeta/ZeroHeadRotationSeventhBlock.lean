/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationSeventhData
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiRotationGridRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadOrdinate1381
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationSeventhWalk00
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationSeventhWalk01
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationSeventhWalk02
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationSeventhWalk03

/-! # Seventh phase-certificate block -/

set_option linter.privateModule false

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- All 145 sequential walks pass the seventh logarithmic block. -/
private theorem phaseSeventhBlock_walks :
    ∀ (i : Fin 29) (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (7181 / 500)
            (phase1381Lower i + (k : ℚ) * (phase1381Upper i - phase1381Lower i) / 4)
            (fun j ↦ phaseSeventhBlockLower j i) (fun j ↦ phaseSeventhBlockUpper j i) 31 =
          true := by
  intro i k hk
  fin_cases i
  · exact phaseSeventhWalk00 k hk
  · exact phaseSeventhWalk01 k hk
  · exact phaseSeventhWalk02 k hk
  · exact phaseSeventhWalk03 k hk
  · exact phaseSeventhWalk04 k hk
  · exact phaseSeventhWalk05 k hk
  · exact phaseSeventhWalk06 k hk
  · exact phaseSeventhWalk07 k hk
  · exact phaseSeventhWalk08 k hk
  · exact phaseSeventhWalk09 k hk
  · exact phaseSeventhWalk10 k hk
  · exact phaseSeventhWalk11 k hk
  · exact phaseSeventhWalk12 k hk
  · exact phaseSeventhWalk13 k hk
  · exact phaseSeventhWalk14 k hk
  · exact phaseSeventhWalk15 k hk
  · exact phaseSeventhWalk16 k hk
  · exact phaseSeventhWalk17 k hk
  · exact phaseSeventhWalk18 k hk
  · exact phaseSeventhWalk19 k hk
  · exact phaseSeventhWalk20 k hk
  · exact phaseSeventhWalk21 k hk
  · exact phaseSeventhWalk22 k hk
  · exact phaseSeventhWalk23 k hk
  · exact phaseSeventhWalk24 k hk
  · exact phaseSeventhWalk25 k hk
  · exact phaseSeventhWalk26 k hk
  · exact phaseSeventhWalk27 k hk
  · exact phaseSeventhWalk28 k hk

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
