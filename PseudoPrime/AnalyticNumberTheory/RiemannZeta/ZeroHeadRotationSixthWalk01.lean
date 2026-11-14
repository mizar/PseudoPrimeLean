/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationSixthData
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiRotationGridRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadOrdinate1381

/-! # Sixth phase-certificate block -/

set_option linter.privateModule false

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The five walks for ordinate bracket 8 pass the sixth block. -/
private theorem phaseSixthWalk08 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (7119 / 500)
            (phase1381Lower (8 : Fin 29) +
              (k : ℚ) * (phase1381Upper (8 : Fin 29) - phase1381Lower (8 : Fin 29)) / 4)
            (fun j ↦ phaseSixthBlockLower j (8 : Fin 29))
            (fun j ↦ phaseSixthBlockUpper j (8 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

/-- The five walks for ordinate bracket 9 pass the sixth block. -/
private theorem phaseSixthWalk09 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (7119 / 500)
            (phase1381Lower (9 : Fin 29) +
              (k : ℚ) * (phase1381Upper (9 : Fin 29) - phase1381Lower (9 : Fin 29)) / 4)
            (fun j ↦ phaseSixthBlockLower j (9 : Fin 29))
            (fun j ↦ phaseSixthBlockUpper j (9 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

/-- The five walks for ordinate bracket 10 pass the sixth block. -/
private theorem phaseSixthWalk10 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (7119 / 500)
            (phase1381Lower (10 : Fin 29) +
              (k : ℚ) * (phase1381Upper (10 : Fin 29) - phase1381Lower (10 : Fin 29)) / 4)
            (fun j ↦ phaseSixthBlockLower j (10 : Fin 29))
            (fun j ↦ phaseSixthBlockUpper j (10 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

/-- The five walks for ordinate bracket 11 pass the sixth block. -/
private theorem phaseSixthWalk11 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (7119 / 500)
            (phase1381Lower (11 : Fin 29) +
              (k : ℚ) * (phase1381Upper (11 : Fin 29) - phase1381Lower (11 : Fin 29)) / 4)
            (fun j ↦ phaseSixthBlockLower j (11 : Fin 29))
            (fun j ↦ phaseSixthBlockUpper j (11 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

/-- The five walks for ordinate bracket 12 pass the sixth block. -/
private theorem phaseSixthWalk12 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (7119 / 500)
            (phase1381Lower (12 : Fin 29) +
              (k : ℚ) * (phase1381Upper (12 : Fin 29) - phase1381Lower (12 : Fin 29)) / 4)
            (fun j ↦ phaseSixthBlockLower j (12 : Fin 29))
            (fun j ↦ phaseSixthBlockUpper j (12 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

/-- The five walks for ordinate bracket 13 pass the sixth block. -/
private theorem phaseSixthWalk13 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (7119 / 500)
            (phase1381Lower (13 : Fin 29) +
              (k : ℚ) * (phase1381Upper (13 : Fin 29) - phase1381Lower (13 : Fin 29)) / 4)
            (fun j ↦ phaseSixthBlockLower j (13 : Fin 29))
            (fun j ↦ phaseSixthBlockUpper j (13 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

/-- The five walks for ordinate bracket 14 pass the sixth block. -/
private theorem phaseSixthWalk14 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (7119 / 500)
            (phase1381Lower (14 : Fin 29) +
              (k : ℚ) * (phase1381Upper (14 : Fin 29) - phase1381Lower (14 : Fin 29)) / 4)
            (fun j ↦ phaseSixthBlockLower j (14 : Fin 29))
            (fun j ↦ phaseSixthBlockUpper j (14 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

/-- The five walks for ordinate bracket 15 pass the sixth block. -/
private theorem phaseSixthWalk15 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (7119 / 500)
            (phase1381Lower (15 : Fin 29) +
              (k : ℚ) * (phase1381Upper (15 : Fin 29) - phase1381Lower (15 : Fin 29)) / 4)
            (fun j ↦ phaseSixthBlockLower j (15 : Fin 29))
            (fun j ↦ phaseSixthBlockUpper j (15 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
