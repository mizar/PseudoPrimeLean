/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationThirteenthData
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiRotationGridRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadOrdinate1381
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationThirteenthWalk00
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationThirteenthWalk01
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationThirteenthWalk02
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationThirteenthWalk03

/-! # Thirteenth phase-certificate block -/

set_option linter.privateModule false

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- All 145 sequential walks pass the thirteenth logarithmic block. -/
private theorem phaseThirteenthBlock_walks :
    ∀ (i : Fin 29) (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (7553 / 500)
            (phase1381Lower i + (k : ℚ) * (phase1381Upper i - phase1381Lower i) / 4)
            (fun j ↦ phaseThirteenthBlockLower j i) (fun j ↦ phaseThirteenthBlockUpper j i) 31 =
          true := by
  intro i k hk
  fin_cases i
  · exact phaseThirteenthWalk00 k hk
  · exact phaseThirteenthWalk01 k hk
  · exact phaseThirteenthWalk02 k hk
  · exact phaseThirteenthWalk03 k hk
  · exact phaseThirteenthWalk04 k hk
  · exact phaseThirteenthWalk05 k hk
  · exact phaseThirteenthWalk06 k hk
  · exact phaseThirteenthWalk07 k hk
  · exact phaseThirteenthWalk08 k hk
  · exact phaseThirteenthWalk09 k hk
  · exact phaseThirteenthWalk10 k hk
  · exact phaseThirteenthWalk11 k hk
  · exact phaseThirteenthWalk12 k hk
  · exact phaseThirteenthWalk13 k hk
  · exact phaseThirteenthWalk14 k hk
  · exact phaseThirteenthWalk15 k hk
  · exact phaseThirteenthWalk16 k hk
  · exact phaseThirteenthWalk17 k hk
  · exact phaseThirteenthWalk18 k hk
  · exact phaseThirteenthWalk19 k hk
  · exact phaseThirteenthWalk20 k hk
  · exact phaseThirteenthWalk21 k hk
  · exact phaseThirteenthWalk22 k hk
  · exact phaseThirteenthWalk23 k hk
  · exact phaseThirteenthWalk24 k hk
  · exact phaseThirteenthWalk25 k hk
  · exact phaseThirteenthWalk26 k hk
  · exact phaseThirteenthWalk27 k hk
  · exact phaseThirteenthWalk28 k hk

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
