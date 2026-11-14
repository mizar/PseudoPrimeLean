/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationNinthData
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiRotationGridRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadOrdinate1381
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationNinthWalk00
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationNinthWalk01
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationNinthWalk02
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationNinthWalk03

/-! # Ninth phase-certificate block -/

set_option linter.privateModule false

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- All 145 sequential walks pass the ninth logarithmic block. -/
private theorem phaseNinthBlock_walks :
    ∀ (i : Fin 29) (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (7305 / 500)
            (phase1381Lower i + (k : ℚ) * (phase1381Upper i - phase1381Lower i) / 4)
            (fun j ↦ phaseNinthBlockLower j i) (fun j ↦ phaseNinthBlockUpper j i) 31 =
          true := by
  intro i k hk
  fin_cases i
  · exact phaseNinthWalk00 k hk
  · exact phaseNinthWalk01 k hk
  · exact phaseNinthWalk02 k hk
  · exact phaseNinthWalk03 k hk
  · exact phaseNinthWalk04 k hk
  · exact phaseNinthWalk05 k hk
  · exact phaseNinthWalk06 k hk
  · exact phaseNinthWalk07 k hk
  · exact phaseNinthWalk08 k hk
  · exact phaseNinthWalk09 k hk
  · exact phaseNinthWalk10 k hk
  · exact phaseNinthWalk11 k hk
  · exact phaseNinthWalk12 k hk
  · exact phaseNinthWalk13 k hk
  · exact phaseNinthWalk14 k hk
  · exact phaseNinthWalk15 k hk
  · exact phaseNinthWalk16 k hk
  · exact phaseNinthWalk17 k hk
  · exact phaseNinthWalk18 k hk
  · exact phaseNinthWalk19 k hk
  · exact phaseNinthWalk20 k hk
  · exact phaseNinthWalk21 k hk
  · exact phaseNinthWalk22 k hk
  · exact phaseNinthWalk23 k hk
  · exact phaseNinthWalk24 k hk
  · exact phaseNinthWalk25 k hk
  · exact phaseNinthWalk26 k hk
  · exact phaseNinthWalk27 k hk
  · exact phaseNinthWalk28 k hk

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
