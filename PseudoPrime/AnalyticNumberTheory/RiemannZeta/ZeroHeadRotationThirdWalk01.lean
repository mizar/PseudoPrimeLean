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

/-- The five walks for ordinate bracket 8 pass the third block. -/
private theorem phaseThirdWalk08 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (6933 / 500)
            (phase1381Lower (8 : Fin 29) +
              (k : ℚ) * (phase1381Upper (8 : Fin 29) - phase1381Lower (8 : Fin 29)) / 4)
            (fun j ↦ phaseThirdBlockLower j (8 : Fin 29))
            (fun j ↦ phaseThirdBlockUpper j (8 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

/-- The five walks for ordinate bracket 9 pass the third block. -/
private theorem phaseThirdWalk09 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (6933 / 500)
            (phase1381Lower (9 : Fin 29) +
              (k : ℚ) * (phase1381Upper (9 : Fin 29) - phase1381Lower (9 : Fin 29)) / 4)
            (fun j ↦ phaseThirdBlockLower j (9 : Fin 29))
            (fun j ↦ phaseThirdBlockUpper j (9 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

/-- The five walks for ordinate bracket 10 pass the third block. -/
private theorem phaseThirdWalk10 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (6933 / 500)
            (phase1381Lower (10 : Fin 29) +
              (k : ℚ) * (phase1381Upper (10 : Fin 29) - phase1381Lower (10 : Fin 29)) / 4)
            (fun j ↦ phaseThirdBlockLower j (10 : Fin 29))
            (fun j ↦ phaseThirdBlockUpper j (10 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

/-- The five walks for ordinate bracket 11 pass the third block. -/
private theorem phaseThirdWalk11 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (6933 / 500)
            (phase1381Lower (11 : Fin 29) +
              (k : ℚ) * (phase1381Upper (11 : Fin 29) - phase1381Lower (11 : Fin 29)) / 4)
            (fun j ↦ phaseThirdBlockLower j (11 : Fin 29))
            (fun j ↦ phaseThirdBlockUpper j (11 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

/-- The five walks for ordinate bracket 12 pass the third block. -/
private theorem phaseThirdWalk12 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (6933 / 500)
            (phase1381Lower (12 : Fin 29) +
              (k : ℚ) * (phase1381Upper (12 : Fin 29) - phase1381Lower (12 : Fin 29)) / 4)
            (fun j ↦ phaseThirdBlockLower j (12 : Fin 29))
            (fun j ↦ phaseThirdBlockUpper j (12 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

/-- The five walks for ordinate bracket 13 pass the third block. -/
private theorem phaseThirdWalk13 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (6933 / 500)
            (phase1381Lower (13 : Fin 29) +
              (k : ℚ) * (phase1381Upper (13 : Fin 29) - phase1381Lower (13 : Fin 29)) / 4)
            (fun j ↦ phaseThirdBlockLower j (13 : Fin 29))
            (fun j ↦ phaseThirdBlockUpper j (13 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

/-- The five walks for ordinate bracket 14 pass the third block. -/
private theorem phaseThirdWalk14 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (6933 / 500)
            (phase1381Lower (14 : Fin 29) +
              (k : ℚ) * (phase1381Upper (14 : Fin 29) - phase1381Lower (14 : Fin 29)) / 4)
            (fun j ↦ phaseThirdBlockLower j (14 : Fin 29))
            (fun j ↦ phaseThirdBlockUpper j (14 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

/-- The five walks for ordinate bracket 15 pass the third block. -/
private theorem phaseThirdWalk15 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (6933 / 500)
            (phase1381Lower (15 : Fin 29) +
              (k : ℚ) * (phase1381Upper (15 : Fin 29) - phase1381Lower (15 : Fin 29)) / 4)
            (fun j ↦ phaseThirdBlockLower j (15 : Fin 29))
            (fun j ↦ phaseThirdBlockUpper j (15 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
