/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock038Data
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiRotationGridRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadOrdinate1381

/-! # Block038 phase-certificate block -/

set_option linter.privateModule false

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The five walks for ordinate bracket 8 pass the block 38 block. -/
private theorem phaseBlock038Walk08 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (9103 / 500)
            (phase1381Lower (8 : Fin 29) +
              (k : ℚ) * (phase1381Upper (8 : Fin 29) - phase1381Lower (8 : Fin 29)) / 4)
            (fun j ↦ phaseBlock038BlockLower j (8 : Fin 29))
            (fun j ↦ phaseBlock038BlockUpper j (8 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

/-- The five walks for ordinate bracket 9 pass the block 38 block. -/
private theorem phaseBlock038Walk09 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (9103 / 500)
            (phase1381Lower (9 : Fin 29) +
              (k : ℚ) * (phase1381Upper (9 : Fin 29) - phase1381Lower (9 : Fin 29)) / 4)
            (fun j ↦ phaseBlock038BlockLower j (9 : Fin 29))
            (fun j ↦ phaseBlock038BlockUpper j (9 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

/-- The five walks for ordinate bracket 10 pass the block 38 block. -/
private theorem phaseBlock038Walk10 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (9103 / 500)
            (phase1381Lower (10 : Fin 29) +
              (k : ℚ) * (phase1381Upper (10 : Fin 29) - phase1381Lower (10 : Fin 29)) / 4)
            (fun j ↦ phaseBlock038BlockLower j (10 : Fin 29))
            (fun j ↦ phaseBlock038BlockUpper j (10 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

/-- The five walks for ordinate bracket 11 pass the block 38 block. -/
private theorem phaseBlock038Walk11 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (9103 / 500)
            (phase1381Lower (11 : Fin 29) +
              (k : ℚ) * (phase1381Upper (11 : Fin 29) - phase1381Lower (11 : Fin 29)) / 4)
            (fun j ↦ phaseBlock038BlockLower j (11 : Fin 29))
            (fun j ↦ phaseBlock038BlockUpper j (11 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

/-- The five walks for ordinate bracket 12 pass the block 38 block. -/
private theorem phaseBlock038Walk12 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (9103 / 500)
            (phase1381Lower (12 : Fin 29) +
              (k : ℚ) * (phase1381Upper (12 : Fin 29) - phase1381Lower (12 : Fin 29)) / 4)
            (fun j ↦ phaseBlock038BlockLower j (12 : Fin 29))
            (fun j ↦ phaseBlock038BlockUpper j (12 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

/-- The five walks for ordinate bracket 13 pass the block 38 block. -/
private theorem phaseBlock038Walk13 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (9103 / 500)
            (phase1381Lower (13 : Fin 29) +
              (k : ℚ) * (phase1381Upper (13 : Fin 29) - phase1381Lower (13 : Fin 29)) / 4)
            (fun j ↦ phaseBlock038BlockLower j (13 : Fin 29))
            (fun j ↦ phaseBlock038BlockUpper j (13 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

/-- The five walks for ordinate bracket 14 pass the block 38 block. -/
private theorem phaseBlock038Walk14 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (9103 / 500)
            (phase1381Lower (14 : Fin 29) +
              (k : ℚ) * (phase1381Upper (14 : Fin 29) - phase1381Lower (14 : Fin 29)) / 4)
            (fun j ↦ phaseBlock038BlockLower j (14 : Fin 29))
            (fun j ↦ phaseBlock038BlockUpper j (14 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

/-- The five walks for ordinate bracket 15 pass the block 38 block. -/
private theorem phaseBlock038Walk15 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (9103 / 500)
            (phase1381Lower (15 : Fin 29) +
              (k : ℚ) * (phase1381Upper (15 : Fin 29) - phase1381Lower (15 : Fin 29)) / 4)
            (fun j ↦ phaseBlock038BlockLower j (15 : Fin 29))
            (fun j ↦ phaseBlock038BlockUpper j (15 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
