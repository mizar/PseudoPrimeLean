/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationTenthData
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiRotationGridRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadOrdinate1381
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationTenthWalk00
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationTenthWalk01
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationTenthWalk02
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationTenthWalk03

/-! # Tenth phase-certificate block -/

set_option linter.privateModule false

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- All 145 sequential walks pass the tenth logarithmic block. -/
private theorem phaseTenthBlock_walks :
    ∀ (i : Fin 29) (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (7367 / 500)
            (phase1381Lower i + (k : ℚ) * (phase1381Upper i - phase1381Lower i) / 4)
            (fun j ↦ phaseTenthBlockLower j i) (fun j ↦ phaseTenthBlockUpper j i) 31 =
          true := by
  intro i k hk
  fin_cases i
  · exact phaseTenthWalk00 k hk
  · exact phaseTenthWalk01 k hk
  · exact phaseTenthWalk02 k hk
  · exact phaseTenthWalk03 k hk
  · exact phaseTenthWalk04 k hk
  · exact phaseTenthWalk05 k hk
  · exact phaseTenthWalk06 k hk
  · exact phaseTenthWalk07 k hk
  · exact phaseTenthWalk08 k hk
  · exact phaseTenthWalk09 k hk
  · exact phaseTenthWalk10 k hk
  · exact phaseTenthWalk11 k hk
  · exact phaseTenthWalk12 k hk
  · exact phaseTenthWalk13 k hk
  · exact phaseTenthWalk14 k hk
  · exact phaseTenthWalk15 k hk
  · exact phaseTenthWalk16 k hk
  · exact phaseTenthWalk17 k hk
  · exact phaseTenthWalk18 k hk
  · exact phaseTenthWalk19 k hk
  · exact phaseTenthWalk20 k hk
  · exact phaseTenthWalk21 k hk
  · exact phaseTenthWalk22 k hk
  · exact phaseTenthWalk23 k hk
  · exact phaseTenthWalk24 k hk
  · exact phaseTenthWalk25 k hk
  · exact phaseTenthWalk26 k hk
  · exact phaseTenthWalk27 k hk
  · exact phaseTenthWalk28 k hk

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
