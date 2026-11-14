/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationThirdData
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiRotationGridRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadOrdinate1381
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationThirdWalk00
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationThirdWalk01
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationThirdWalk02
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationThirdWalk03

/-! # Third phase-certificate block -/

set_option linter.privateModule false

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- All 145 sequential walks pass the third logarithmic block. -/
private theorem phaseThirdBlock_walks :
    ∀ (i : Fin 29) (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (6933 / 500)
            (phase1381Lower i + (k : ℚ) * (phase1381Upper i - phase1381Lower i) / 4)
            (fun j ↦ phaseThirdBlockLower j i) (fun j ↦ phaseThirdBlockUpper j i) 31 =
          true := by
  intro i k hk
  fin_cases i
  · exact phaseThirdWalk00 k hk
  · exact phaseThirdWalk01 k hk
  · exact phaseThirdWalk02 k hk
  · exact phaseThirdWalk03 k hk
  · exact phaseThirdWalk04 k hk
  · exact phaseThirdWalk05 k hk
  · exact phaseThirdWalk06 k hk
  · exact phaseThirdWalk07 k hk
  · exact phaseThirdWalk08 k hk
  · exact phaseThirdWalk09 k hk
  · exact phaseThirdWalk10 k hk
  · exact phaseThirdWalk11 k hk
  · exact phaseThirdWalk12 k hk
  · exact phaseThirdWalk13 k hk
  · exact phaseThirdWalk14 k hk
  · exact phaseThirdWalk15 k hk
  · exact phaseThirdWalk16 k hk
  · exact phaseThirdWalk17 k hk
  · exact phaseThirdWalk18 k hk
  · exact phaseThirdWalk19 k hk
  · exact phaseThirdWalk20 k hk
  · exact phaseThirdWalk21 k hk
  · exact phaseThirdWalk22 k hk
  · exact phaseThirdWalk23 k hk
  · exact phaseThirdWalk24 k hk
  · exact phaseThirdWalk25 k hk
  · exact phaseThirdWalk26 k hk
  · exact phaseThirdWalk27 k hk
  · exact phaseThirdWalk28 k hk

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
