/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationFourthData
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiRotationGridRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadOrdinate1381

/-! # Fourth phase-certificate block -/

set_option linter.privateModule false

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The five walks for ordinate bracket 0 pass the fourth block. -/
private theorem phaseFourthWalk00 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (1399 / 100)
            (phase1381Lower (0 : Fin 29) +
              (k : ℚ) * (phase1381Upper (0 : Fin 29) - phase1381Lower (0 : Fin 29)) / 4)
            (fun j ↦ phaseFourthBlockLower j (0 : Fin 29))
            (fun j ↦ phaseFourthBlockUpper j (0 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

/-- The five walks for ordinate bracket 1 pass the fourth block. -/
private theorem phaseFourthWalk01 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (1399 / 100)
            (phase1381Lower (1 : Fin 29) +
              (k : ℚ) * (phase1381Upper (1 : Fin 29) - phase1381Lower (1 : Fin 29)) / 4)
            (fun j ↦ phaseFourthBlockLower j (1 : Fin 29))
            (fun j ↦ phaseFourthBlockUpper j (1 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

/-- The five walks for ordinate bracket 2 pass the fourth block. -/
private theorem phaseFourthWalk02 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (1399 / 100)
            (phase1381Lower (2 : Fin 29) +
              (k : ℚ) * (phase1381Upper (2 : Fin 29) - phase1381Lower (2 : Fin 29)) / 4)
            (fun j ↦ phaseFourthBlockLower j (2 : Fin 29))
            (fun j ↦ phaseFourthBlockUpper j (2 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

/-- The five walks for ordinate bracket 3 pass the fourth block. -/
private theorem phaseFourthWalk03 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (1399 / 100)
            (phase1381Lower (3 : Fin 29) +
              (k : ℚ) * (phase1381Upper (3 : Fin 29) - phase1381Lower (3 : Fin 29)) / 4)
            (fun j ↦ phaseFourthBlockLower j (3 : Fin 29))
            (fun j ↦ phaseFourthBlockUpper j (3 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

/-- The five walks for ordinate bracket 4 pass the fourth block. -/
private theorem phaseFourthWalk04 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (1399 / 100)
            (phase1381Lower (4 : Fin 29) +
              (k : ℚ) * (phase1381Upper (4 : Fin 29) - phase1381Lower (4 : Fin 29)) / 4)
            (fun j ↦ phaseFourthBlockLower j (4 : Fin 29))
            (fun j ↦ phaseFourthBlockUpper j (4 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

/-- The five walks for ordinate bracket 5 pass the fourth block. -/
private theorem phaseFourthWalk05 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (1399 / 100)
            (phase1381Lower (5 : Fin 29) +
              (k : ℚ) * (phase1381Upper (5 : Fin 29) - phase1381Lower (5 : Fin 29)) / 4)
            (fun j ↦ phaseFourthBlockLower j (5 : Fin 29))
            (fun j ↦ phaseFourthBlockUpper j (5 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

/-- The five walks for ordinate bracket 6 pass the fourth block. -/
private theorem phaseFourthWalk06 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (1399 / 100)
            (phase1381Lower (6 : Fin 29) +
              (k : ℚ) * (phase1381Upper (6 : Fin 29) - phase1381Lower (6 : Fin 29)) / 4)
            (fun j ↦ phaseFourthBlockLower j (6 : Fin 29))
            (fun j ↦ phaseFourthBlockUpper j (6 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

/-- The five walks for ordinate bracket 7 pass the fourth block. -/
private theorem phaseFourthWalk07 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (1399 / 100)
            (phase1381Lower (7 : Fin 29) +
              (k : ℚ) * (phase1381Upper (7 : Fin 29) - phase1381Lower (7 : Fin 29)) / 4)
            (fun j ↦ phaseFourthBlockLower j (7 : Fin 29))
            (fun j ↦ phaseFourthBlockUpper j (7 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
