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

-- Kernel reduction sums the previously checked finite logarithm endpoints.
/-- The checked logarithm upper endpoints through 1000 sum to at most 996.7. -/
theorem quarter_psi1000_rows_997 :
    ((centerRowsBelow 1000).map (fun r ↦ r.hi)).sum ≤ (9967 / 10 : ℚ) := by decide +kernel

/-- The existing checked prime-power rows give the unconditional upper bound
`psi 1000 ≤ 996.7`. This improves the boundary term in Euler-tail estimates. -/
theorem quarter_psi1000_997 : Chebyshev.psi 1000 ≤ 9967 / 10 := by
  have hz : ∀ n, ¬IsPrimePow n → ArithmeticFunction.vonMangoldt n = 0 := by
    intro n hn
    exact ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn
  have h :=
    checked_rows_mangoldt_upper (centerRowsBelow 1000) (9967 / 10) (centerRowsBelow_check 1000)
      quarter_psi1000_rows_997
  rw [← centerRowsBelow_sum _ hz (by decide)] at h
  simp only [Chebyshev.psi, Nat.floor_ofNat]
  simpa only [Rat.cast_div, Rat.cast_ofNat] using h

end PseudoPrime.PrimeTestBounds.MillerRabin
