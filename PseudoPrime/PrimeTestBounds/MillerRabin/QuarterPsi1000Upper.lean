/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerLogSumUpper
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerCutoffRows

/-! # Chebyshev upper boundary at 1000 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

set_option maxRecDepth 30000 in
-- Kernel reduction sums the previously checked finite logarithm endpoints.
/-- The checked logarithm upper endpoints through 1000 sum to at most 1000. -/
theorem quarter_psi1000_rows_upper :
    ((centerRowsBelow 1000).map (fun r ↦ r.hi)).sum ≤ (1000 : ℚ) := by decide +kernel

/-- The existing checked prime-power rows give the unconditional upper bound
`psi 1000 ≤ 1000`. This improves the boundary term in Euler-tail estimates. -/
theorem quarter_psi1000_upper : Chebyshev.psi 1000 ≤ 1000 := by
  have hz : ∀ n, ¬IsPrimePow n → ArithmeticFunction.vonMangoldt n = 0 := by
    intro n hn
    exact ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn
  have h :=
    checked_rows_mangoldt_upper (centerRowsBelow 1000) 1000 (centerRowsBelow_check 1000)
      quarter_psi1000_rows_upper
  rw [← centerRowsBelow_sum _ hz (by decide)] at h
  simp only [Chebyshev.psi, Nat.floor_ofNat]
  simpa only [Rat.cast_ofNat] using h

end PseudoPrime.PrimeTestBounds.MillerRabin
