/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentLower2701

/-! # Reflected moment lower endpoint, degree 1 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

-- The finite calculation retains the independently checked prime-power rows.
-- Exact rational arithmetic verifies this independent moment endpoint.
/-- The rational degree-1 moment prefix exceeds its explicit lower endpoint. -/
theorem quarter_moment_lower_cap1 :
    (2662 / 1000 : ℚ) ≤
      (List.zipWith (fun r u ↦ r.lo * (((r.k + 1 : ℕ) : ℚ) * r.lo) ^ 1 * u) (centerRowsBelow 2701)
          quarterMomentLower2701).sum := by
  decide +kernel

/-- The actual finite degree-1 Mangoldt moment exceeds the certified lower endpoint. -/
theorem quarter_moment_lower_real1 :
    (2662 / 1000 : ℝ) ≤ ∑ n ∈ Finset.Ioc 0 2701, quarterMangoldtMoment 1 n := by
  have h := (Rat.cast_le (K := ℝ)).mpr quarter_moment_lower_cap1
  simp only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h.trans (quarter_moment_lower2701 1)

end PseudoPrime.PrimeTestBounds.MillerRabin
