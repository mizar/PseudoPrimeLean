/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationFourthData
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiRotationGridRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadOrdinate1381
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationFourthWalk00
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationFourthWalk01
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationFourthWalk02
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationFourthWalk03

/-! # Fourth phase-certificate block -/

set_option linter.privateModule false

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- All 145 sequential walks pass the fourth logarithmic block. -/
private theorem phaseFourthBlock_walks :
    ∀ (i : Fin 29) (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (1399 / 100)
            (phase1381Lower i + (k : ℚ) * (phase1381Upper i - phase1381Lower i) / 4)
            (fun j ↦ phaseFourthBlockLower j i) (fun j ↦ phaseFourthBlockUpper j i) 31 =
          true := by
  intro i k hk
  fin_cases i
  · exact phaseFourthWalk00 k hk
  · exact phaseFourthWalk01 k hk
  · exact phaseFourthWalk02 k hk
  · exact phaseFourthWalk03 k hk
  · exact phaseFourthWalk04 k hk
  · exact phaseFourthWalk05 k hk
  · exact phaseFourthWalk06 k hk
  · exact phaseFourthWalk07 k hk
  · exact phaseFourthWalk08 k hk
  · exact phaseFourthWalk09 k hk
  · exact phaseFourthWalk10 k hk
  · exact phaseFourthWalk11 k hk
  · exact phaseFourthWalk12 k hk
  · exact phaseFourthWalk13 k hk
  · exact phaseFourthWalk14 k hk
  · exact phaseFourthWalk15 k hk
  · exact phaseFourthWalk16 k hk
  · exact phaseFourthWalk17 k hk
  · exact phaseFourthWalk18 k hk
  · exact phaseFourthWalk19 k hk
  · exact phaseFourthWalk20 k hk
  · exact phaseFourthWalk21 k hk
  · exact phaseFourthWalk22 k hk
  · exact phaseFourthWalk23 k hk
  · exact phaseFourthWalk24 k hk
  · exact phaseFourthWalk25 k hk
  · exact phaseFourthWalk26 k hk
  · exact phaseFourthWalk27 k hk
  · exact phaseFourthWalk28 k hk

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
