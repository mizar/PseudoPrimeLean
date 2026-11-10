/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentPrefix2701
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerLogSum

/-! # Chebyshev boundary at the moment cutoff -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

-- Kernel reduction sums the certified logarithm lower endpoints through 2701.
set_option maxRecDepth 30000 in
-- This scalar check is independent of the six moment prefix checks.
/-- The sum of existing logarithm endpoints exceeds 2702.944613. -/
theorem quarter_psi2701_rows_lower :
    (2702944613 / 1000000 : ℚ) ≤ ((centerRowsBelow 2701).map (fun r ↦ r.lo)).sum := by
  decide +kernel

/-- The checked prime-power rows give an unconditional lower bound for
`psi 2701`. The exact finite-support identity retains the boundary term
required by the refined moment-tail estimate. -/
theorem quarter_psi2701_lower : (2702944613 / 1000000 : ℝ) ≤ Chebyshev.psi 2701 := by
  have hz : ∀ n, ¬IsPrimePow n → ArithmeticFunction.vonMangoldt n = 0 := by
    intro n hn
    exact ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn
  have h :=
    checked_rows_mangoldt_lower (centerRowsBelow 2701) (2702944613 / 1000000)
      (centerRowsBelow_check 2701) quarter_psi2701_rows_lower
  rw [← centerRowsBelow_sum _ hz (by decide)] at h
  simp only [Chebyshev.psi, Nat.floor_ofNat]
  simpa only [Rat.cast_div, Rat.cast_ofNat] using h

end PseudoPrime.PrimeTestBounds.MillerRabin
