/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.MeanCountingBudget

/-! # Rational scalar gaps for average-logarithm counting

Each cell checks a rational endpoint and transfers the resulting gap to its full interval
of positive logarithmic scales.
-/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For `0 < u ≤ 28` and `L ≥ 80000`, the first cell's scalar gap exceeds the
loss budget 120. Check a rational gap at 28 and use monotonicity in `u`.
This feeds the first average-logarithm counting cell. -/
theorem mean_scalar_gap_one {u L : ℝ} (hu : 0 < u) (huU : u ≤ 28) (hL : 80000 ≤ L) :
    (1 - (13069 / 20000 : ℝ)) * L + 120 <
      ((13069 / 20000 : ℝ) / (10029 / 10000)) *
        ((9968 / 10000) / 2 + ((999 / 1000) * (9968 / 10000) + (15 * (993 / 1000) / 16) / 2) / u +
          ((999 / 1000) * (15 * (993 / 1000) / 16)) / u ^ 2) *
        L := by
  apply
    mean_gap_of_endpoint (U := 28) (g := 129 / 10000) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) hu huU (by linarith only [hL]) (by norm_num only)
  linarith only [hL]

/-- For `0 < u ≤ 38` and `L ≥ 1000000`, the second cell's scalar gap exceeds
the loss budget 120. A rational endpoint check and monotonicity cover the cell.
This feeds the second average-logarithm counting cell. -/
theorem mean_scalar_gap_two {u L : ℝ} (hu : 0 < u) (huU : u ≤ 38) (hL : 1000000 ≤ L) :
    (1 - (13069 / 20000 : ℝ)) * L + 120 <
      ((13069 / 20000 : ℝ) / (10008 / 10000)) *
        ((9991 / 10000) / 2 + ((999 / 1000) * (9991 / 10000) + (15 * (9983 / 10000) / 16) / 2) / u +
          ((999 / 1000) * (15 * (9983 / 10000) / 16)) / u ^ 2) *
        L := by
  apply
    mean_gap_of_endpoint (U := 38) (g := 52 / 10000) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) hu huU (by linarith only [hL]) (by norm_num only)
  linarith only [hL]

/-- For `0 < u ≤ 48` and `L ≥ 100000000`, the third cell's scalar gap exceeds
the loss budget 120. A rational endpoint check and monotonicity cover the cell.
This feeds the third average-logarithm counting cell. -/
theorem mean_scalar_gap_three {u L : ℝ} (hu : 0 < u) (huU : u ≤ 48) (hL : 100000000 ≤ L) :
    (1 - (13069 / 20000 : ℝ)) * L + 120 <
      ((13069 / 20000 : ℝ) / (100008 / 100000)) *
        ((99992 / 100000) / 2 +
          ((999 / 1000) * (99992 / 100000) + (15 * (99984 / 100000) / 16) / 2) / u +
          ((999 / 1000) * (15 * (99984 / 100000) / 16)) / u ^ 2) *
        L := by
  apply
    mean_gap_of_endpoint (U := 48) (g := 36 / 100000) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) hu huU (by linarith only [hL]) (by norm_num only)
  linarith only [hL]

end PseudoPrime.PrimeTestBounds.MillerRabin
