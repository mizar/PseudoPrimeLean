/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.WeightedGroupSum
public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed373Data
public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed1849Data

/-! # Certified grouped counts through 1849 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A checked grid extends any supplied base-count lower bounds with an arbitrary
number of equal-weight labels. -/
theorem target028_group_grid_general (p r N m : ℕ) (hp : 0 < p) (hr : r < p) (base row : Array ℕ)
    (rows : List (Array ℕ)) (hlen : rows.length = m)
    (hb : ∀ k ≤ N, base.getD k 0 ≤ weightedPrimeCount id primeSeed373Weights (r + k * p))
    (hrows : weightedGroupRowsCheck N base row rows = true) :
    row.getD N 0 ≤
      weightedPrimeCount id (List.replicate m p ++ primeSeed373Weights) (r + N * p) := by
  exact weightedGroupRows_lower p r N m primeSeed373Weights base row rows hp hr hlen hb hrows

/-- A checked short grid combines all numbers of the 209 added labels, given
lower bounds for its base entries. -/
theorem target028_group_grid_lower (r N : ℕ) (hr : r < 76) (base row : Array ℕ)
    (rows : List (Array ℕ)) (hlen : rows.length = 209)
    (hb : ∀ k ≤ N, base.getD k 0 ≤ weightedPrimeCount id primeSeed373Weights (r + k * 76))
    (hrows : weightedGroupRowsCheck N base row rows = true) :
    row.getD N 0 ≤ weightedPrimeCount id primeSeed1849Weights (r + N * 76) := by
  have hgrid := weightedGroupRowsCheck_sound N base row rows hrows N (le_refl N)
  rw [hlen] at hgrid
  rw [hgrid]
  exact
    weightedGroupGrid_le 76 r primeSeed373Weights (fun k ↦ base.getD k 0) (by decide) hr N hb 209 N
      (le_refl N)

end PseudoPrime.PrimeTestBounds.MillerRabin
