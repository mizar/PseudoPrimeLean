/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentPrefix2701

/-! # Certified finite Mangoldt moment, degree 0 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

-- The kernel reduces the distinct degree-0 rational prefix over the finite support.
set_option maxRecDepth 30000 in
-- Exact rational arithmetic verifies this moment's independent scalar bound.
/-- The rational degree-0 moment prefix is below its explicit upper endpoint. -/
theorem quarter_moment_prefix2701_cap0 :
    (List.zipWith (fun r u ↦ r.hi * (((r.k + 1 : ℕ) : ℚ) * r.hi) ^ 0 * u) (centerRowsBelow 2701)
          quarterMomentPowers2701).sum ≤
      (1223136 / 1000000 : ℚ) := by
  decide +kernel

/-- The actual finite degree-0 Mangoldt moment satisfies the certified bound. -/
theorem quarter_moment_prefix2701_real0 :
    (∑ n ∈ Finset.Ioc 0 2701, quarterMangoldtMoment 0 n) ≤ (1223136 / 1000000 : ℝ) := by
  have h := (Rat.cast_le (K := ℝ)).mpr quarter_moment_prefix2701_cap0
  simp only [Rat.cast_div, Rat.cast_ofNat] at h
  exact (quarter_moment_prefix2701_upper 0).trans h

end PseudoPrime.PrimeTestBounds.MillerRabin
