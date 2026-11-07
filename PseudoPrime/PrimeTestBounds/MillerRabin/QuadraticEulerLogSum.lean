/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerRowArithmetic

/-! # Chebyshev lower sums from checked Euler rows -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A rational lower sum of logarithm endpoints bounds the actual Mangoldt
sum on checked rows. Apply the individual logarithm bounds and cast the
rational sum. This reuses Euler certificates for the Chebyshev boundary. -/
theorem checked_rows_mangoldt_lower (rows : List EulerCenterRow) (L : ℚ)
    (hc : rows.all eulerCenterRowCheck = true) (hl : L ≤ (rows.map (fun r ↦ r.lo)).sum) :
    (L : ℝ) ≤ (rows.map (fun r ↦ ArithmeticFunction.vonMangoldt (r.p ^ (r.k + 1)))).sum := by
  have ha :
    (rows.map (fun r ↦ (r.lo : ℝ))).sum ≤
      (rows.map (fun r ↦ ArithmeticFunction.vonMangoldt (r.p ^ (r.k + 1)))).sum := by
    apply List.sum_le_sum
    intro r hr
    have h := List.all_eq_true.mp hc r hr
    rw [checked_row_mangoldt_eq_log h]
    exact (checked_row_log_bounds h).1
  have hR := (Rat.cast_le (K := ℝ)).mpr hl
  simp only [Rat.cast_list_sum, List.map_map, Function.comp_def] at hR
  exact hR.trans ha

end PseudoPrime.PrimeTestBounds.MillerRabin
