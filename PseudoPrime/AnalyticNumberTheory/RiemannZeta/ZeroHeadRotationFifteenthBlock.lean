/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationFifteenthData
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiRotationGridRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadOrdinate1381
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationFifteenthWalk00
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationFifteenthWalk01
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationFifteenthWalk02
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationFifteenthWalk03

/-! # Fifteenth phase-certificate block -/

set_option linter.privateModule false

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- All 145 sequential walks pass the fifteenth logarithmic block. -/
private theorem phaseFifteenthBlock_walks :
    ∀ (i : Fin 29) (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (7677 / 500)
            (phase1381Lower i + (k : ℚ) * (phase1381Upper i - phase1381Lower i) / 4)
            (fun j ↦ phaseFifteenthBlockLower j i) (fun j ↦ phaseFifteenthBlockUpper j i) 31 =
          true := by
  intro i k hk
  fin_cases i
  · exact phaseFifteenthWalk00 k hk
  · exact phaseFifteenthWalk01 k hk
  · exact phaseFifteenthWalk02 k hk
  · exact phaseFifteenthWalk03 k hk
  · exact phaseFifteenthWalk04 k hk
  · exact phaseFifteenthWalk05 k hk
  · exact phaseFifteenthWalk06 k hk
  · exact phaseFifteenthWalk07 k hk
  · exact phaseFifteenthWalk08 k hk
  · exact phaseFifteenthWalk09 k hk
  · exact phaseFifteenthWalk10 k hk
  · exact phaseFifteenthWalk11 k hk
  · exact phaseFifteenthWalk12 k hk
  · exact phaseFifteenthWalk13 k hk
  · exact phaseFifteenthWalk14 k hk
  · exact phaseFifteenthWalk15 k hk
  · exact phaseFifteenthWalk16 k hk
  · exact phaseFifteenthWalk17 k hk
  · exact phaseFifteenthWalk18 k hk
  · exact phaseFifteenthWalk19 k hk
  · exact phaseFifteenthWalk20 k hk
  · exact phaseFifteenthWalk21 k hk
  · exact phaseFifteenthWalk22 k hk
  · exact phaseFifteenthWalk23 k hk
  · exact phaseFifteenthWalk24 k hk
  · exact phaseFifteenthWalk25 k hk
  · exact phaseFifteenthWalk26 k hk
  · exact phaseFifteenthWalk27 k hk
  · exact phaseFifteenthWalk28 k hk

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
