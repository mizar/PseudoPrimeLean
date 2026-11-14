/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationEighthData
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiRotationGridRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadOrdinate1381
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationEighthWalk00
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationEighthWalk01
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationEighthWalk02
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationEighthWalk03

/-! # Eighth phase-certificate block -/

set_option linter.privateModule false

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- All 145 sequential walks pass the eighth logarithmic block. -/
private theorem phaseEighthBlock_walks :
    ∀ (i : Fin 29) (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (7243 / 500)
            (phase1381Lower i + (k : ℚ) * (phase1381Upper i - phase1381Lower i) / 4)
            (fun j ↦ phaseEighthBlockLower j i) (fun j ↦ phaseEighthBlockUpper j i) 31 =
          true := by
  intro i k hk
  fin_cases i
  · exact phaseEighthWalk00 k hk
  · exact phaseEighthWalk01 k hk
  · exact phaseEighthWalk02 k hk
  · exact phaseEighthWalk03 k hk
  · exact phaseEighthWalk04 k hk
  · exact phaseEighthWalk05 k hk
  · exact phaseEighthWalk06 k hk
  · exact phaseEighthWalk07 k hk
  · exact phaseEighthWalk08 k hk
  · exact phaseEighthWalk09 k hk
  · exact phaseEighthWalk10 k hk
  · exact phaseEighthWalk11 k hk
  · exact phaseEighthWalk12 k hk
  · exact phaseEighthWalk13 k hk
  · exact phaseEighthWalk14 k hk
  · exact phaseEighthWalk15 k hk
  · exact phaseEighthWalk16 k hk
  · exact phaseEighthWalk17 k hk
  · exact phaseEighthWalk18 k hk
  · exact phaseEighthWalk19 k hk
  · exact phaseEighthWalk20 k hk
  · exact phaseEighthWalk21 k hk
  · exact phaseEighthWalk22 k hk
  · exact phaseEighthWalk23 k hk
  · exact phaseEighthWalk24 k hk
  · exact phaseEighthWalk25 k hk
  · exact phaseEighthWalk26 k hk
  · exact phaseEighthWalk27 k hk
  · exact phaseEighthWalk28 k hk

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
