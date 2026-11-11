/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerLogSum
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerCutoffRows

/-! # Lower Chebyshev bounds from checked finite rows -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A certified rational lower sum for checked rows through `B ≤ 50000` gives
an unconditional lower bound for `psi B`. Exact support transfers the row sum. -/
theorem quarter_psi_rows_lower {B : ℕ} (hB : B ≤ 50000) (L : ℚ)
    (hl : L ≤ ((centerRowsBelow B).map (fun r ↦ r.lo)).sum) : (L : ℝ) ≤ Chebyshev.psi B := by
  have hz : ∀ n, ¬IsPrimePow n → ArithmeticFunction.vonMangoldt n = 0 := by
    intro n hn
    exact ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn
  have h := checked_rows_mangoldt_lower (centerRowsBelow B) L (centerRowsBelow_check B) hl
  rw [← centerRowsBelow_sum _ hz hB] at h
  simpa only [Chebyshev.psi, Nat.floor_natCast] using h

end PseudoPrime.PrimeTestBounds.MillerRabin
