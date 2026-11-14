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

/-- The five walks for ordinate bracket 16 pass the sixth block. -/
private theorem phaseSixthWalk16 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (7119 / 500)
            (phase1381Lower (16 : Fin 29) +
              (k : ℚ) * (phase1381Upper (16 : Fin 29) - phase1381Lower (16 : Fin 29)) / 4)
            (fun j ↦ phaseSixthBlockLower j (16 : Fin 29))
            (fun j ↦ phaseSixthBlockUpper j (16 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

/-- The five walks for ordinate bracket 17 pass the sixth block. -/
private theorem phaseSixthWalk17 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (7119 / 500)
            (phase1381Lower (17 : Fin 29) +
              (k : ℚ) * (phase1381Upper (17 : Fin 29) - phase1381Lower (17 : Fin 29)) / 4)
            (fun j ↦ phaseSixthBlockLower j (17 : Fin 29))
            (fun j ↦ phaseSixthBlockUpper j (17 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

/-- The five walks for ordinate bracket 18 pass the sixth block. -/
private theorem phaseSixthWalk18 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (7119 / 500)
            (phase1381Lower (18 : Fin 29) +
              (k : ℚ) * (phase1381Upper (18 : Fin 29) - phase1381Lower (18 : Fin 29)) / 4)
            (fun j ↦ phaseSixthBlockLower j (18 : Fin 29))
            (fun j ↦ phaseSixthBlockUpper j (18 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

/-- The five walks for ordinate bracket 19 pass the sixth block. -/
private theorem phaseSixthWalk19 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (7119 / 500)
            (phase1381Lower (19 : Fin 29) +
              (k : ℚ) * (phase1381Upper (19 : Fin 29) - phase1381Lower (19 : Fin 29)) / 4)
            (fun j ↦ phaseSixthBlockLower j (19 : Fin 29))
            (fun j ↦ phaseSixthBlockUpper j (19 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

/-- The five walks for ordinate bracket 20 pass the sixth block. -/
private theorem phaseSixthWalk20 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (7119 / 500)
            (phase1381Lower (20 : Fin 29) +
              (k : ℚ) * (phase1381Upper (20 : Fin 29) - phase1381Lower (20 : Fin 29)) / 4)
            (fun j ↦ phaseSixthBlockLower j (20 : Fin 29))
            (fun j ↦ phaseSixthBlockUpper j (20 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

/-- The five walks for ordinate bracket 21 pass the sixth block. -/
private theorem phaseSixthWalk21 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (7119 / 500)
            (phase1381Lower (21 : Fin 29) +
              (k : ℚ) * (phase1381Upper (21 : Fin 29) - phase1381Lower (21 : Fin 29)) / 4)
            (fun j ↦ phaseSixthBlockLower j (21 : Fin 29))
            (fun j ↦ phaseSixthBlockUpper j (21 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

/-- The five walks for ordinate bracket 22 pass the sixth block. -/
private theorem phaseSixthWalk22 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (7119 / 500)
            (phase1381Lower (22 : Fin 29) +
              (k : ℚ) * (phase1381Upper (22 : Fin 29) - phase1381Lower (22 : Fin 29)) / 4)
            (fun j ↦ phaseSixthBlockLower j (22 : Fin 29))
            (fun j ↦ phaseSixthBlockUpper j (22 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

/-- The five walks for ordinate bracket 23 pass the sixth block. -/
private theorem phaseSixthWalk23 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (7119 / 500)
            (phase1381Lower (23 : Fin 29) +
              (k : ℚ) * (phase1381Upper (23 : Fin 29) - phase1381Lower (23 : Fin 29)) / 4)
            (fun j ↦ phaseSixthBlockLower j (23 : Fin 29))
            (fun j ↦ phaseSixthBlockUpper j (23 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
