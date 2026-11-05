/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.MeanScalarCells

/-! # Scalar gaps for the short mean-counting bridge -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The first mean-counting cell has a strict scalar gap above scale `80000`.
The endpoint rational budget transfers to the whole cell. -/
theorem short_scalar_gap_one {u L : ℝ} (hu : 0 < u) (huU : u ≤ 28) (hL : 80000 ≤ L) :
    (1 - (3251 / 5000 : ℝ)) * L + 120 <
      ((3251 / 5000 : ℝ) / (10029 / 10000)) *
        ((9968 / 10000) / 2 + ((999 / 1000) * (9968 / 10000) + (15 * (993 / 1000) / 16) / 2) / u +
          ((999 / 1000) * (15 * (993 / 1000) / 16)) / u ^ 2) *
        L := by
  apply
    mean_gap_of_endpoint (U := 28) (g := 79 / 10000) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) hu huU (by linarith only [hL]) (by norm_num only)
  linarith only [hL]

/-- The second mean-counting cell has a strict scalar gap above scale `10 ^ 6`.
The endpoint rational budget transfers to the whole cell. -/
theorem short_scalar_gap_two {u L : ℝ} (hu : 0 < u) (huU : u ≤ 38) (hL : 1000000 ≤ L) :
    (1 - (3251 / 5000 : ℝ)) * L + 120 <
      ((3251 / 5000 : ℝ) / (10008 / 10000)) *
        ((9991 / 10000) / 2 + ((999 / 1000) * (9991 / 10000) + (15 * (9983 / 10000) / 16) / 2) / u +
          ((999 / 1000) * (15 * (9983 / 10000) / 16)) / u ^ 2) *
        L := by
  apply
    mean_gap_of_endpoint (U := 38) (g := 23 / 100000) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) hu huU (by linarith only [hL]) (by norm_num only)
  linarith only [hL]

/-- The third mean-counting cell has a strict scalar gap above scale `10 ^ 8`.
The endpoint rational budget transfers to the whole cell. -/
theorem short_scalar_gap_three {u L : ℝ} (hu : 0 < u) (huU : u ≤ 38) (hL : 100000000 ≤ L) :
    (1 - (3251 / 5000 : ℝ)) * L + 120 <
      ((3251 / 5000 : ℝ) / (100008 / 100000)) *
        ((99992 / 100000) / 2 +
          ((999 / 1000) * (99992 / 100000) + (15 * (99984 / 100000) / 16) / 2) / u +
          ((999 / 1000) * (15 * (99984 / 100000) / 16)) / u ^ 2) *
        L := by
  apply
    mean_gap_of_endpoint (U := 38) (g := 77 / 100000) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) hu huU (by linarith only [hL]) (by norm_num only)
  linarith only [hL]



end PseudoPrime.PrimeTestBounds.MillerRabin
