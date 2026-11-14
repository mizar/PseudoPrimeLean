/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationThirdData
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiRotationGridRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadOrdinate1381

/-! # Third phase-certificate block -/

set_option linter.privateModule false

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The five walks for ordinate bracket 24 pass the third block. -/
private theorem phaseThirdWalk24 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (6933 / 500)
            (phase1381Lower (24 : Fin 29) +
              (k : ℚ) * (phase1381Upper (24 : Fin 29) - phase1381Lower (24 : Fin 29)) / 4)
            (fun j ↦ phaseThirdBlockLower j (24 : Fin 29))
            (fun j ↦ phaseThirdBlockUpper j (24 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

/-- The five walks for ordinate bracket 25 pass the third block. -/
private theorem phaseThirdWalk25 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (6933 / 500)
            (phase1381Lower (25 : Fin 29) +
              (k : ℚ) * (phase1381Upper (25 : Fin 29) - phase1381Lower (25 : Fin 29)) / 4)
            (fun j ↦ phaseThirdBlockLower j (25 : Fin 29))
            (fun j ↦ phaseThirdBlockUpper j (25 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

/-- The five walks for ordinate bracket 26 pass the third block. -/
private theorem phaseThirdWalk26 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (6933 / 500)
            (phase1381Lower (26 : Fin 29) +
              (k : ℚ) * (phase1381Upper (26 : Fin 29) - phase1381Lower (26 : Fin 29)) / 4)
            (fun j ↦ phaseThirdBlockLower j (26 : Fin 29))
            (fun j ↦ phaseThirdBlockUpper j (26 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

/-- The five walks for ordinate bracket 27 pass the third block. -/
private theorem phaseThirdWalk27 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (6933 / 500)
            (phase1381Lower (27 : Fin 29) +
              (k : ℚ) * (phase1381Upper (27 : Fin 29) - phase1381Lower (27 : Fin 29)) / 4)
            (fun j ↦ phaseThirdBlockLower j (27 : Fin 29))
            (fun j ↦ phaseThirdBlockUpper j (27 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

/-- The five walks for ordinate bracket 28 pass the third block. -/
private theorem phaseThirdWalk28 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (6933 / 500)
            (phase1381Lower (28 : Fin 29) +
              (k : ℚ) * (phase1381Upper (28 : Fin 29) - phase1381Lower (28 : Fin 29)) / 4)
            (fun j ↦ phaseThirdBlockLower j (28 : Fin 29))
            (fun j ↦ phaseThirdBlockUpper j (28 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
