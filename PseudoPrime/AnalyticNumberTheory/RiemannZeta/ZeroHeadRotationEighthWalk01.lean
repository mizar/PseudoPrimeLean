/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationEighthData
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiRotationGridRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadOrdinate1381

/-! # Eighth phase-certificate block -/

set_option linter.privateModule false

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The five walks for ordinate bracket 8 pass the eighth block. -/
private theorem phaseEighthWalk08 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (7243 / 500)
            (phase1381Lower (8 : Fin 29) +
              (k : ℚ) * (phase1381Upper (8 : Fin 29) - phase1381Lower (8 : Fin 29)) / 4)
            (fun j ↦ phaseEighthBlockLower j (8 : Fin 29))
            (fun j ↦ phaseEighthBlockUpper j (8 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

/-- The five walks for ordinate bracket 9 pass the eighth block. -/
private theorem phaseEighthWalk09 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (7243 / 500)
            (phase1381Lower (9 : Fin 29) +
              (k : ℚ) * (phase1381Upper (9 : Fin 29) - phase1381Lower (9 : Fin 29)) / 4)
            (fun j ↦ phaseEighthBlockLower j (9 : Fin 29))
            (fun j ↦ phaseEighthBlockUpper j (9 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

/-- The five walks for ordinate bracket 10 pass the eighth block. -/
private theorem phaseEighthWalk10 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (7243 / 500)
            (phase1381Lower (10 : Fin 29) +
              (k : ℚ) * (phase1381Upper (10 : Fin 29) - phase1381Lower (10 : Fin 29)) / 4)
            (fun j ↦ phaseEighthBlockLower j (10 : Fin 29))
            (fun j ↦ phaseEighthBlockUpper j (10 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

/-- The five walks for ordinate bracket 11 pass the eighth block. -/
private theorem phaseEighthWalk11 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (7243 / 500)
            (phase1381Lower (11 : Fin 29) +
              (k : ℚ) * (phase1381Upper (11 : Fin 29) - phase1381Lower (11 : Fin 29)) / 4)
            (fun j ↦ phaseEighthBlockLower j (11 : Fin 29))
            (fun j ↦ phaseEighthBlockUpper j (11 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

/-- The five walks for ordinate bracket 12 pass the eighth block. -/
private theorem phaseEighthWalk12 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (7243 / 500)
            (phase1381Lower (12 : Fin 29) +
              (k : ℚ) * (phase1381Upper (12 : Fin 29) - phase1381Lower (12 : Fin 29)) / 4)
            (fun j ↦ phaseEighthBlockLower j (12 : Fin 29))
            (fun j ↦ phaseEighthBlockUpper j (12 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

/-- The five walks for ordinate bracket 13 pass the eighth block. -/
private theorem phaseEighthWalk13 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (7243 / 500)
            (phase1381Lower (13 : Fin 29) +
              (k : ℚ) * (phase1381Upper (13 : Fin 29) - phase1381Lower (13 : Fin 29)) / 4)
            (fun j ↦ phaseEighthBlockLower j (13 : Fin 29))
            (fun j ↦ phaseEighthBlockUpper j (13 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

/-- The five walks for ordinate bracket 14 pass the eighth block. -/
private theorem phaseEighthWalk14 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (7243 / 500)
            (phase1381Lower (14 : Fin 29) +
              (k : ℚ) * (phase1381Upper (14 : Fin 29) - phase1381Lower (14 : Fin 29)) / 4)
            (fun j ↦ phaseEighthBlockLower j (14 : Fin 29))
            (fun j ↦ phaseEighthBlockUpper j (14 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

/-- The five walks for ordinate bracket 15 pass the eighth block. -/
private theorem phaseEighthWalk15 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (7243 / 500)
            (phase1381Lower (15 : Fin 29) +
              (k : ℚ) * (phase1381Upper (15 : Fin 29) - phase1381Lower (15 : Fin 29)) / 4)
            (fun j ↦ phaseEighthBlockLower j (15 : Fin 29))
            (fun j ↦ phaseEighthBlockUpper j (15 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
