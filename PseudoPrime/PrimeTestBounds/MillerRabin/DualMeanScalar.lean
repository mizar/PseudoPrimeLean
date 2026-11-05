/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.MeanScalarCells
/-! # Scalar gaps for the short dual-scale mean bridge -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin
/-- The first mean-counting cell has a strict gap from scale 81000.
A rational endpoint estimate covers the full interval of logarithmic radii. -/
theorem dualMean_gap_one {u L : ℝ} (hu : 0 < u) (huU : u ≤ 28) (hL : 81000 ≤ L) :
    (1 - (647 / 1000 : ℝ)) * L + 120 <
      ((647 / 1000 : ℝ) / (10029 / 10000)) *
        ((9968 / 10000) / 2 + ((999 / 1000) * (9968 / 10000) + (15 * (993 / 1000) / 16) / 2) / u +
          ((999 / 1000) * (15 * (993 / 1000) / 16)) / u ^ 2) *
        L := by
  apply mean_gap_of_endpoint (U := 28) (g := 1482 / 1000000)
    (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
    hu huU (by linarith only [hL]) (by norm_num only)
  linarith only [hL]
/-- The second mean-counting cell has a strict gap from scale 1010000.
A rational endpoint estimate covers the full interval of logarithmic radii. -/
theorem dualMean_gap_two {u L : ℝ} (hu : 0 < u) (huU : u ≤ 31) (hL : 1010000 ≤ L) :
    (1 - (647 / 1000 : ℝ)) * L + 120 <
      ((647 / 1000 : ℝ) / (10008 / 10000)) *
        ((9991 / 10000) / 2 + ((999 / 1000) * (9991 / 10000) + (15 * (9983 / 10000) / 16) / 2) / u +
          ((999 / 1000) * (15 * (9983 / 10000) / 16)) / u ^ 2) *
        L := by
  apply mean_gap_of_endpoint (U := 31) (g := 1 / 1000)
    (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
    hu huU (by linarith only [hL]) (by norm_num only)
  linarith only [hL]
end PseudoPrime.PrimeTestBounds.MillerRabin
