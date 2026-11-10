/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerLogSum

/-! # Chebyshev upper sums from checked Euler rows -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A rational upper sum of checked logarithm endpoints bounds the Mangoldt
sum on the same rows. Each row's existing logarithm certificate is reused. -/
theorem checked_rows_mangoldt_upper (rows : List EulerCenterRow) (U : ℚ)
    (hc : rows.all eulerCenterRowCheck = true) (hu : (rows.map (fun r ↦ r.hi)).sum ≤ U) :
    (rows.map (fun r ↦ ArithmeticFunction.vonMangoldt (r.p ^ (r.k + 1)))).sum ≤ (U : ℝ) := by
  have ha :
    (rows.map (fun r ↦ ArithmeticFunction.vonMangoldt (r.p ^ (r.k + 1)))).sum ≤
      (rows.map (fun r ↦ (r.hi : ℝ))).sum := by
    apply List.sum_le_sum
    intro r hr
    have h := List.all_eq_true.mp hc r hr
    rw [checked_row_mangoldt_eq_log h]
    exact (checked_row_log_bounds h).2
  have hR := (Rat.cast_le (K := ℝ)).mpr hu
  simp only [Rat.cast_list_sum, List.map_map, Function.comp_def] at hR
  exact ha.trans hR

end PseudoPrime.PrimeTestBounds.MillerRabin
