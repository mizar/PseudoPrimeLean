/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationSixteenthData
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiRotationGridRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadOrdinate1381
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationSixteenthWalk00
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationSixteenthWalk01
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationSixteenthWalk02
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationSixteenthWalk03

/-! # Sixteenth phase-certificate block -/

set_option linter.privateModule false

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- All 145 sequential walks pass the sixteenth logarithmic block. -/
private theorem phaseSixteenthBlock_walks :
    ∀ (i : Fin 29) (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (7739 / 500)
            (phase1381Lower i + (k : ℚ) * (phase1381Upper i - phase1381Lower i) / 4)
            (fun j ↦ phaseSixteenthBlockLower j i) (fun j ↦ phaseSixteenthBlockUpper j i) 31 =
          true := by
  intro i k hk
  fin_cases i
  · exact phaseSixteenthWalk00 k hk
  · exact phaseSixteenthWalk01 k hk
  · exact phaseSixteenthWalk02 k hk
  · exact phaseSixteenthWalk03 k hk
  · exact phaseSixteenthWalk04 k hk
  · exact phaseSixteenthWalk05 k hk
  · exact phaseSixteenthWalk06 k hk
  · exact phaseSixteenthWalk07 k hk
  · exact phaseSixteenthWalk08 k hk
  · exact phaseSixteenthWalk09 k hk
  · exact phaseSixteenthWalk10 k hk
  · exact phaseSixteenthWalk11 k hk
  · exact phaseSixteenthWalk12 k hk
  · exact phaseSixteenthWalk13 k hk
  · exact phaseSixteenthWalk14 k hk
  · exact phaseSixteenthWalk15 k hk
  · exact phaseSixteenthWalk16 k hk
  · exact phaseSixteenthWalk17 k hk
  · exact phaseSixteenthWalk18 k hk
  · exact phaseSixteenthWalk19 k hk
  · exact phaseSixteenthWalk20 k hk
  · exact phaseSixteenthWalk21 k hk
  · exact phaseSixteenthWalk22 k hk
  · exact phaseSixteenthWalk23 k hk
  · exact phaseSixteenthWalk24 k hk
  · exact phaseSixteenthWalk25 k hk
  · exact phaseSixteenthWalk26 k hk
  · exact phaseSixteenthWalk27 k hk
  · exact phaseSixteenthWalk28 k hk

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
