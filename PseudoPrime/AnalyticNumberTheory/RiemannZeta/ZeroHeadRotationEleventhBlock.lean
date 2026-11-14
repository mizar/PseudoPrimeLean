/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationEleventhData
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiRotationGridRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadOrdinate1381
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationEleventhWalk00
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationEleventhWalk01
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationEleventhWalk02
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationEleventhWalk03

/-! # Eleventh phase-certificate block -/

set_option linter.privateModule false

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- All 145 sequential walks pass the eleventh logarithmic block. -/
private theorem phaseEleventhBlock_walks :
    ∀ (i : Fin 29) (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (7429 / 500)
            (phase1381Lower i + (k : ℚ) * (phase1381Upper i - phase1381Lower i) / 4)
            (fun j ↦ phaseEleventhBlockLower j i) (fun j ↦ phaseEleventhBlockUpper j i) 31 =
          true := by
  intro i k hk
  fin_cases i
  · exact phaseEleventhWalk00 k hk
  · exact phaseEleventhWalk01 k hk
  · exact phaseEleventhWalk02 k hk
  · exact phaseEleventhWalk03 k hk
  · exact phaseEleventhWalk04 k hk
  · exact phaseEleventhWalk05 k hk
  · exact phaseEleventhWalk06 k hk
  · exact phaseEleventhWalk07 k hk
  · exact phaseEleventhWalk08 k hk
  · exact phaseEleventhWalk09 k hk
  · exact phaseEleventhWalk10 k hk
  · exact phaseEleventhWalk11 k hk
  · exact phaseEleventhWalk12 k hk
  · exact phaseEleventhWalk13 k hk
  · exact phaseEleventhWalk14 k hk
  · exact phaseEleventhWalk15 k hk
  · exact phaseEleventhWalk16 k hk
  · exact phaseEleventhWalk17 k hk
  · exact phaseEleventhWalk18 k hk
  · exact phaseEleventhWalk19 k hk
  · exact phaseEleventhWalk20 k hk
  · exact phaseEleventhWalk21 k hk
  · exact phaseEleventhWalk22 k hk
  · exact phaseEleventhWalk23 k hk
  · exact phaseEleventhWalk24 k hk
  · exact phaseEleventhWalk25 k hk
  · exact phaseEleventhWalk26 k hk
  · exact phaseEleventhWalk27 k hk
  · exact phaseEleventhWalk28 k hk

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
