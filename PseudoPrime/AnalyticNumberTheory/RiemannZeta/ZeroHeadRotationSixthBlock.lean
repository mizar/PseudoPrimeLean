/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationSixthData
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiRotationGridRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadOrdinate1381
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationSixthWalk00
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationSixthWalk01
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationSixthWalk02
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationSixthWalk03

/-! # Sixth phase-certificate block -/

set_option linter.privateModule false

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- All 145 sequential walks pass the sixth logarithmic block. -/
private theorem phaseSixthBlock_walks :
    ∀ (i : Fin 29) (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (7119 / 500)
            (phase1381Lower i + (k : ℚ) * (phase1381Upper i - phase1381Lower i) / 4)
            (fun j ↦ phaseSixthBlockLower j i) (fun j ↦ phaseSixthBlockUpper j i) 31 =
          true := by
  intro i k hk
  fin_cases i
  · exact phaseSixthWalk00 k hk
  · exact phaseSixthWalk01 k hk
  · exact phaseSixthWalk02 k hk
  · exact phaseSixthWalk03 k hk
  · exact phaseSixthWalk04 k hk
  · exact phaseSixthWalk05 k hk
  · exact phaseSixthWalk06 k hk
  · exact phaseSixthWalk07 k hk
  · exact phaseSixthWalk08 k hk
  · exact phaseSixthWalk09 k hk
  · exact phaseSixthWalk10 k hk
  · exact phaseSixthWalk11 k hk
  · exact phaseSixthWalk12 k hk
  · exact phaseSixthWalk13 k hk
  · exact phaseSixthWalk14 k hk
  · exact phaseSixthWalk15 k hk
  · exact phaseSixthWalk16 k hk
  · exact phaseSixthWalk17 k hk
  · exact phaseSixthWalk18 k hk
  · exact phaseSixthWalk19 k hk
  · exact phaseSixthWalk20 k hk
  · exact phaseSixthWalk21 k hk
  · exact phaseSixthWalk22 k hk
  · exact phaseSixthWalk23 k hk
  · exact phaseSixthWalk24 k hk
  · exact phaseSixthWalk25 k hk
  · exact phaseSixthWalk26 k hk
  · exact phaseSixthWalk27 k hk
  · exact phaseSixthWalk28 k hk

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
