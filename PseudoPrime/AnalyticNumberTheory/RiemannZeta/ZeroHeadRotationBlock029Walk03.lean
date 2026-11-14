/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock029Data
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiRotationGridRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadOrdinate1381

/-! # Block029 phase-certificate block -/

set_option linter.privateModule false

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The five walks for ordinate bracket 24 pass the block 29 block. -/
private theorem phaseBlock029Walk24 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (8545 / 500)
            (phase1381Lower (24 : Fin 29) +
              (k : ℚ) * (phase1381Upper (24 : Fin 29) - phase1381Lower (24 : Fin 29)) / 4)
            (fun j ↦ phaseBlock029BlockLower j (24 : Fin 29))
            (fun j ↦ phaseBlock029BlockUpper j (24 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

/-- The five walks for ordinate bracket 25 pass the block 29 block. -/
private theorem phaseBlock029Walk25 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (8545 / 500)
            (phase1381Lower (25 : Fin 29) +
              (k : ℚ) * (phase1381Upper (25 : Fin 29) - phase1381Lower (25 : Fin 29)) / 4)
            (fun j ↦ phaseBlock029BlockLower j (25 : Fin 29))
            (fun j ↦ phaseBlock029BlockUpper j (25 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

/-- The five walks for ordinate bracket 26 pass the block 29 block. -/
private theorem phaseBlock029Walk26 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (8545 / 500)
            (phase1381Lower (26 : Fin 29) +
              (k : ℚ) * (phase1381Upper (26 : Fin 29) - phase1381Lower (26 : Fin 29)) / 4)
            (fun j ↦ phaseBlock029BlockLower j (26 : Fin 29))
            (fun j ↦ phaseBlock029BlockUpper j (26 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

/-- The five walks for ordinate bracket 27 pass the block 29 block. -/
private theorem phaseBlock029Walk27 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (8545 / 500)
            (phase1381Lower (27 : Fin 29) +
              (k : ℚ) * (phase1381Upper (27 : Fin 29) - phase1381Lower (27 : Fin 29)) / 4)
            (fun j ↦ phaseBlock029BlockLower j (27 : Fin 29))
            (fun j ↦ phaseBlock029BlockUpper j (27 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

/-- The five walks for ordinate bracket 28 pass the block 29 block. -/
private theorem phaseBlock029Walk28 :
    ∀ (k : ℕ),
      k ≤ 4 →
        rotationOrdinateGridCheck (8545 / 500)
            (phase1381Lower (28 : Fin 29) +
              (k : ℚ) * (phase1381Upper (28 : Fin 29) - phase1381Lower (28 : Fin 29)) / 4)
            (fun j ↦ phaseBlock029BlockLower j (28 : Fin 29))
            (fun j ↦ phaseBlock029BlockUpper j (28 : Fin 29)) 31 =
          true := by
  intro k hk
  interval_cases k <;> decide +kernel

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
