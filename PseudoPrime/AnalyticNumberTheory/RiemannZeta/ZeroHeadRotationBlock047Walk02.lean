/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock047Data
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiRotationGridRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadOrdinate1381

/-! # Block047 phase-certificate block -/

set_option linter.privateModule false

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The five walks for ordinate bracket 16 pass the block 47 block. -/
private theorem phaseBlock047Walk16 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (9661 / 500)
            (phase1381Lower (16 : Fin 29) +
              (k : ℚ) * (phase1381Upper (16 : Fin 29) - phase1381Lower (16 : Fin 29)) / 4)
            (fun j ↦ phaseBlock047BlockLower j (16 : Fin 29))
            (fun j ↦ phaseBlock047BlockUpper j (16 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

/-- The five walks for ordinate bracket 17 pass the block 47 block. -/
private theorem phaseBlock047Walk17 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (9661 / 500)
            (phase1381Lower (17 : Fin 29) +
              (k : ℚ) * (phase1381Upper (17 : Fin 29) - phase1381Lower (17 : Fin 29)) / 4)
            (fun j ↦ phaseBlock047BlockLower j (17 : Fin 29))
            (fun j ↦ phaseBlock047BlockUpper j (17 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

/-- The five walks for ordinate bracket 18 pass the block 47 block. -/
private theorem phaseBlock047Walk18 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (9661 / 500)
            (phase1381Lower (18 : Fin 29) +
              (k : ℚ) * (phase1381Upper (18 : Fin 29) - phase1381Lower (18 : Fin 29)) / 4)
            (fun j ↦ phaseBlock047BlockLower j (18 : Fin 29))
            (fun j ↦ phaseBlock047BlockUpper j (18 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

/-- The five walks for ordinate bracket 19 pass the block 47 block. -/
private theorem phaseBlock047Walk19 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (9661 / 500)
            (phase1381Lower (19 : Fin 29) +
              (k : ℚ) * (phase1381Upper (19 : Fin 29) - phase1381Lower (19 : Fin 29)) / 4)
            (fun j ↦ phaseBlock047BlockLower j (19 : Fin 29))
            (fun j ↦ phaseBlock047BlockUpper j (19 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

/-- The five walks for ordinate bracket 20 pass the block 47 block. -/
private theorem phaseBlock047Walk20 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (9661 / 500)
            (phase1381Lower (20 : Fin 29) +
              (k : ℚ) * (phase1381Upper (20 : Fin 29) - phase1381Lower (20 : Fin 29)) / 4)
            (fun j ↦ phaseBlock047BlockLower j (20 : Fin 29))
            (fun j ↦ phaseBlock047BlockUpper j (20 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

/-- The five walks for ordinate bracket 21 pass the block 47 block. -/
private theorem phaseBlock047Walk21 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (9661 / 500)
            (phase1381Lower (21 : Fin 29) +
              (k : ℚ) * (phase1381Upper (21 : Fin 29) - phase1381Lower (21 : Fin 29)) / 4)
            (fun j ↦ phaseBlock047BlockLower j (21 : Fin 29))
            (fun j ↦ phaseBlock047BlockUpper j (21 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

/-- The five walks for ordinate bracket 22 pass the block 47 block. -/
private theorem phaseBlock047Walk22 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (9661 / 500)
            (phase1381Lower (22 : Fin 29) +
              (k : ℚ) * (phase1381Upper (22 : Fin 29) - phase1381Lower (22 : Fin 29)) / 4)
            (fun j ↦ phaseBlock047BlockLower j (22 : Fin 29))
            (fun j ↦ phaseBlock047BlockUpper j (22 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

/-- The five walks for ordinate bracket 23 pass the block 47 block. -/
private theorem phaseBlock047Walk23 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (9661 / 500)
            (phase1381Lower (23 : Fin 29) +
              (k : ℚ) * (phase1381Upper (23 : Fin 29) - phase1381Lower (23 : Fin 29)) / 4)
            (fun j ↦ phaseBlock047BlockLower j (23 : Fin 29))
            (fun j ↦ phaseBlock047BlockUpper j (23 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
