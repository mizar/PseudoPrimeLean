/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationNinthData
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiRotationGridRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadOrdinate1381

/-! # Ninth phase-certificate block -/

set_option linter.privateModule false

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The five walks for ordinate bracket 16 pass the ninth block. -/
private theorem phaseNinthWalk16 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (7305 / 500)
            (phase1381Lower (16 : Fin 29) +
              (k : ℚ) * (phase1381Upper (16 : Fin 29) - phase1381Lower (16 : Fin 29)) / 4)
            (fun j ↦ phaseNinthBlockLower j (16 : Fin 29))
            (fun j ↦ phaseNinthBlockUpper j (16 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

/-- The five walks for ordinate bracket 17 pass the ninth block. -/
private theorem phaseNinthWalk17 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (7305 / 500)
            (phase1381Lower (17 : Fin 29) +
              (k : ℚ) * (phase1381Upper (17 : Fin 29) - phase1381Lower (17 : Fin 29)) / 4)
            (fun j ↦ phaseNinthBlockLower j (17 : Fin 29))
            (fun j ↦ phaseNinthBlockUpper j (17 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

/-- The five walks for ordinate bracket 18 pass the ninth block. -/
private theorem phaseNinthWalk18 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (7305 / 500)
            (phase1381Lower (18 : Fin 29) +
              (k : ℚ) * (phase1381Upper (18 : Fin 29) - phase1381Lower (18 : Fin 29)) / 4)
            (fun j ↦ phaseNinthBlockLower j (18 : Fin 29))
            (fun j ↦ phaseNinthBlockUpper j (18 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

/-- The five walks for ordinate bracket 19 pass the ninth block. -/
private theorem phaseNinthWalk19 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (7305 / 500)
            (phase1381Lower (19 : Fin 29) +
              (k : ℚ) * (phase1381Upper (19 : Fin 29) - phase1381Lower (19 : Fin 29)) / 4)
            (fun j ↦ phaseNinthBlockLower j (19 : Fin 29))
            (fun j ↦ phaseNinthBlockUpper j (19 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

/-- The five walks for ordinate bracket 20 pass the ninth block. -/
private theorem phaseNinthWalk20 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (7305 / 500)
            (phase1381Lower (20 : Fin 29) +
              (k : ℚ) * (phase1381Upper (20 : Fin 29) - phase1381Lower (20 : Fin 29)) / 4)
            (fun j ↦ phaseNinthBlockLower j (20 : Fin 29))
            (fun j ↦ phaseNinthBlockUpper j (20 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

/-- The five walks for ordinate bracket 21 pass the ninth block. -/
private theorem phaseNinthWalk21 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (7305 / 500)
            (phase1381Lower (21 : Fin 29) +
              (k : ℚ) * (phase1381Upper (21 : Fin 29) - phase1381Lower (21 : Fin 29)) / 4)
            (fun j ↦ phaseNinthBlockLower j (21 : Fin 29))
            (fun j ↦ phaseNinthBlockUpper j (21 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

/-- The five walks for ordinate bracket 22 pass the ninth block. -/
private theorem phaseNinthWalk22 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (7305 / 500)
            (phase1381Lower (22 : Fin 29) +
              (k : ℚ) * (phase1381Upper (22 : Fin 29) - phase1381Lower (22 : Fin 29)) / 4)
            (fun j ↦ phaseNinthBlockLower j (22 : Fin 29))
            (fun j ↦ phaseNinthBlockUpper j (22 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

/-- The five walks for ordinate bracket 23 pass the ninth block. -/
private theorem phaseNinthWalk23 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (7305 / 500)
            (phase1381Lower (23 : Fin 29) +
              (k : ℚ) * (phase1381Upper (23 : Fin 29) - phase1381Lower (23 : Fin 29)) / 4)
            (fun j ↦ phaseNinthBlockLower j (23 : Fin 29))
            (fun j ↦ phaseNinthBlockUpper j (23 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
