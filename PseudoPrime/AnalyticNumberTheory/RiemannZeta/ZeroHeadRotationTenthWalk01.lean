/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationTenthData
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiRotationGridRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadOrdinate1381

/-! # Tenth phase-certificate block -/

set_option linter.privateModule false

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The five walks for ordinate bracket 8 pass the tenth block. -/
private theorem phaseTenthWalk08 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (7367 / 500)
            (phase1381Lower (8 : Fin 29) +
              (k : ℚ) * (phase1381Upper (8 : Fin 29) - phase1381Lower (8 : Fin 29)) / 4)
            (fun j ↦ phaseTenthBlockLower j (8 : Fin 29))
            (fun j ↦ phaseTenthBlockUpper j (8 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

/-- The five walks for ordinate bracket 9 pass the tenth block. -/
private theorem phaseTenthWalk09 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (7367 / 500)
            (phase1381Lower (9 : Fin 29) +
              (k : ℚ) * (phase1381Upper (9 : Fin 29) - phase1381Lower (9 : Fin 29)) / 4)
            (fun j ↦ phaseTenthBlockLower j (9 : Fin 29))
            (fun j ↦ phaseTenthBlockUpper j (9 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

/-- The five walks for ordinate bracket 10 pass the tenth block. -/
private theorem phaseTenthWalk10 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (7367 / 500)
            (phase1381Lower (10 : Fin 29) +
              (k : ℚ) * (phase1381Upper (10 : Fin 29) - phase1381Lower (10 : Fin 29)) / 4)
            (fun j ↦ phaseTenthBlockLower j (10 : Fin 29))
            (fun j ↦ phaseTenthBlockUpper j (10 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

/-- The five walks for ordinate bracket 11 pass the tenth block. -/
private theorem phaseTenthWalk11 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (7367 / 500)
            (phase1381Lower (11 : Fin 29) +
              (k : ℚ) * (phase1381Upper (11 : Fin 29) - phase1381Lower (11 : Fin 29)) / 4)
            (fun j ↦ phaseTenthBlockLower j (11 : Fin 29))
            (fun j ↦ phaseTenthBlockUpper j (11 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

/-- The five walks for ordinate bracket 12 pass the tenth block. -/
private theorem phaseTenthWalk12 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (7367 / 500)
            (phase1381Lower (12 : Fin 29) +
              (k : ℚ) * (phase1381Upper (12 : Fin 29) - phase1381Lower (12 : Fin 29)) / 4)
            (fun j ↦ phaseTenthBlockLower j (12 : Fin 29))
            (fun j ↦ phaseTenthBlockUpper j (12 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

/-- The five walks for ordinate bracket 13 pass the tenth block. -/
private theorem phaseTenthWalk13 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (7367 / 500)
            (phase1381Lower (13 : Fin 29) +
              (k : ℚ) * (phase1381Upper (13 : Fin 29) - phase1381Lower (13 : Fin 29)) / 4)
            (fun j ↦ phaseTenthBlockLower j (13 : Fin 29))
            (fun j ↦ phaseTenthBlockUpper j (13 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

/-- The five walks for ordinate bracket 14 pass the tenth block. -/
private theorem phaseTenthWalk14 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (7367 / 500)
            (phase1381Lower (14 : Fin 29) +
              (k : ℚ) * (phase1381Upper (14 : Fin 29) - phase1381Lower (14 : Fin 29)) / 4)
            (fun j ↦ phaseTenthBlockLower j (14 : Fin 29))
            (fun j ↦ phaseTenthBlockUpper j (14 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

/-- The five walks for ordinate bracket 15 pass the tenth block. -/
private theorem phaseTenthWalk15 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (7367 / 500)
            (phase1381Lower (15 : Fin 29) +
              (k : ℚ) * (phase1381Upper (15 : Fin 29) - phase1381Lower (15 : Fin 29)) / 4)
            (fun j ↦ phaseTenthBlockLower j (15 : Fin 29))
            (fun j ↦ phaseTenthBlockUpper j (15 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
