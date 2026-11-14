/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationFourteenthData
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiRotationGridRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadOrdinate1381
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationFourteenthWalk00
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationFourteenthWalk01
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationFourteenthWalk02
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationFourteenthWalk03

/-! # Fourteenth phase-certificate block -/

set_option linter.privateModule false

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- All 145 sequential walks pass the fourteenth logarithmic block. -/
private theorem phaseFourteenthBlock_walks :
    ∀ (i : Fin 29) (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (7615 / 500)
            (phase1381Lower i + (k : ℚ) * (phase1381Upper i - phase1381Lower i) / 4)
            (fun j ↦ phaseFourteenthBlockLower j i) (fun j ↦ phaseFourteenthBlockUpper j i) 31 =
          true := by
  intro i k hk
  fin_cases i
  · exact phaseFourteenthWalk00 k hk
  · exact phaseFourteenthWalk01 k hk
  · exact phaseFourteenthWalk02 k hk
  · exact phaseFourteenthWalk03 k hk
  · exact phaseFourteenthWalk04 k hk
  · exact phaseFourteenthWalk05 k hk
  · exact phaseFourteenthWalk06 k hk
  · exact phaseFourteenthWalk07 k hk
  · exact phaseFourteenthWalk08 k hk
  · exact phaseFourteenthWalk09 k hk
  · exact phaseFourteenthWalk10 k hk
  · exact phaseFourteenthWalk11 k hk
  · exact phaseFourteenthWalk12 k hk
  · exact phaseFourteenthWalk13 k hk
  · exact phaseFourteenthWalk14 k hk
  · exact phaseFourteenthWalk15 k hk
  · exact phaseFourteenthWalk16 k hk
  · exact phaseFourteenthWalk17 k hk
  · exact phaseFourteenthWalk18 k hk
  · exact phaseFourteenthWalk19 k hk
  · exact phaseFourteenthWalk20 k hk
  · exact phaseFourteenthWalk21 k hk
  · exact phaseFourteenthWalk22 k hk
  · exact phaseFourteenthWalk23 k hk
  · exact phaseFourteenthWalk24 k hk
  · exact phaseFourteenthWalk25 k hk
  · exact phaseFourteenthWalk26 k hk
  · exact phaseFourteenthWalk27 k hk
  · exact phaseFourteenthWalk28 k hk

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
