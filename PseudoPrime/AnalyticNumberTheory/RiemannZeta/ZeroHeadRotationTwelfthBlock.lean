/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationTwelfthData
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiRotationGridRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadOrdinate1381
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationTwelfthWalk00
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationTwelfthWalk01
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationTwelfthWalk02
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationTwelfthWalk03

/-! # Twelfth phase-certificate block -/

set_option linter.privateModule false

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- All 145 sequential walks pass the twelfth logarithmic block. -/
private theorem phaseTwelfthBlock_walks :
    ∀ (i : Fin 29) (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (7491 / 500)
            (phase1381Lower i + (k : ℚ) * (phase1381Upper i - phase1381Lower i) / 4)
            (fun j ↦ phaseTwelfthBlockLower j i) (fun j ↦ phaseTwelfthBlockUpper j i) 31 =
          true := by
  intro i k hk
  fin_cases i
  · exact phaseTwelfthWalk00 k hk
  · exact phaseTwelfthWalk01 k hk
  · exact phaseTwelfthWalk02 k hk
  · exact phaseTwelfthWalk03 k hk
  · exact phaseTwelfthWalk04 k hk
  · exact phaseTwelfthWalk05 k hk
  · exact phaseTwelfthWalk06 k hk
  · exact phaseTwelfthWalk07 k hk
  · exact phaseTwelfthWalk08 k hk
  · exact phaseTwelfthWalk09 k hk
  · exact phaseTwelfthWalk10 k hk
  · exact phaseTwelfthWalk11 k hk
  · exact phaseTwelfthWalk12 k hk
  · exact phaseTwelfthWalk13 k hk
  · exact phaseTwelfthWalk14 k hk
  · exact phaseTwelfthWalk15 k hk
  · exact phaseTwelfthWalk16 k hk
  · exact phaseTwelfthWalk17 k hk
  · exact phaseTwelfthWalk18 k hk
  · exact phaseTwelfthWalk19 k hk
  · exact phaseTwelfthWalk20 k hk
  · exact phaseTwelfthWalk21 k hk
  · exact phaseTwelfthWalk22 k hk
  · exact phaseTwelfthWalk23 k hk
  · exact phaseTwelfthWalk24 k hk
  · exact phaseTwelfthWalk25 k hk
  · exact phaseTwelfthWalk26 k hk
  · exact phaseTwelfthWalk27 k hk
  · exact phaseTwelfthWalk28 k hk

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
