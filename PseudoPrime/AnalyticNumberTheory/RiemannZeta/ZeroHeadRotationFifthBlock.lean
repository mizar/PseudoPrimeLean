/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationFifthData
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiRotationGridRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadOrdinate1381
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationFifthWalk00
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationFifthWalk01
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationFifthWalk02
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationFifthWalk03

/-! # Fifth phase-certificate block -/

set_option linter.privateModule false

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- All 145 sequential walks pass the fifth logarithmic block. -/
private theorem phaseFifthBlock_walks :
    ∀ (i : Fin 29) (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (7057 / 500)
            (phase1381Lower i + (k : ℚ) * (phase1381Upper i - phase1381Lower i) / 4)
            (fun j ↦ phaseFifthBlockLower j i) (fun j ↦ phaseFifthBlockUpper j i) 31 =
          true := by
  intro i k hk
  fin_cases i
  · exact phaseFifthWalk00 k hk
  · exact phaseFifthWalk01 k hk
  · exact phaseFifthWalk02 k hk
  · exact phaseFifthWalk03 k hk
  · exact phaseFifthWalk04 k hk
  · exact phaseFifthWalk05 k hk
  · exact phaseFifthWalk06 k hk
  · exact phaseFifthWalk07 k hk
  · exact phaseFifthWalk08 k hk
  · exact phaseFifthWalk09 k hk
  · exact phaseFifthWalk10 k hk
  · exact phaseFifthWalk11 k hk
  · exact phaseFifthWalk12 k hk
  · exact phaseFifthWalk13 k hk
  · exact phaseFifthWalk14 k hk
  · exact phaseFifthWalk15 k hk
  · exact phaseFifthWalk16 k hk
  · exact phaseFifthWalk17 k hk
  · exact phaseFifthWalk18 k hk
  · exact phaseFifthWalk19 k hk
  · exact phaseFifthWalk20 k hk
  · exact phaseFifthWalk21 k hk
  · exact phaseFifthWalk22 k hk
  · exact phaseFifthWalk23 k hk
  · exact phaseFifthWalk24 k hk
  · exact phaseFifthWalk25 k hk
  · exact phaseFifthWalk26 k hk
  · exact phaseFifthWalk27 k hk
  · exact phaseFifthWalk28 k hk

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
