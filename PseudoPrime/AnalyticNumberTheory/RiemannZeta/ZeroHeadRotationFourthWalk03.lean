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

/-- The five walks for ordinate bracket 24 pass the fourth block. -/
private theorem phaseFourthWalk24 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (1399 / 100)
            (phase1381Lower (24 : Fin 29) +
              (k : ℚ) * (phase1381Upper (24 : Fin 29) - phase1381Lower (24 : Fin 29)) / 4)
            (fun j ↦ phaseFourthBlockLower j (24 : Fin 29))
            (fun j ↦ phaseFourthBlockUpper j (24 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

/-- The five walks for ordinate bracket 25 pass the fourth block. -/
private theorem phaseFourthWalk25 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (1399 / 100)
            (phase1381Lower (25 : Fin 29) +
              (k : ℚ) * (phase1381Upper (25 : Fin 29) - phase1381Lower (25 : Fin 29)) / 4)
            (fun j ↦ phaseFourthBlockLower j (25 : Fin 29))
            (fun j ↦ phaseFourthBlockUpper j (25 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

/-- The five walks for ordinate bracket 26 pass the fourth block. -/
private theorem phaseFourthWalk26 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (1399 / 100)
            (phase1381Lower (26 : Fin 29) +
              (k : ℚ) * (phase1381Upper (26 : Fin 29) - phase1381Lower (26 : Fin 29)) / 4)
            (fun j ↦ phaseFourthBlockLower j (26 : Fin 29))
            (fun j ↦ phaseFourthBlockUpper j (26 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

/-- The five walks for ordinate bracket 27 pass the fourth block. -/
private theorem phaseFourthWalk27 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (1399 / 100)
            (phase1381Lower (27 : Fin 29) +
              (k : ℚ) * (phase1381Upper (27 : Fin 29) - phase1381Lower (27 : Fin 29)) / 4)
            (fun j ↦ phaseFourthBlockLower j (27 : Fin 29))
            (fun j ↦ phaseFourthBlockUpper j (27 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

/-- The five walks for ordinate bracket 28 pass the fourth block. -/
private theorem phaseFourthWalk28 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (1399 / 100)
            (phase1381Lower (28 : Fin 29) +
              (k : ℚ) * (phase1381Upper (28 : Fin 29) - phase1381Lower (28 : Fin 29)) / 4)
            (fun j ↦ phaseFourthBlockLower j (28 : Fin 29))
            (fun j ↦ phaseFourthBlockUpper j (28 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
