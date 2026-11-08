/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.WeightedGroupSum
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030Semiprime100

/-! # Certified grouped counts through 1849 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A checked grid samples the existing base count and adds any number of
equal-weight labels. The cap 500 preserves the base-row lower bound at larger
budgets by monotonicity. -/
theorem target028_group_grid_general (p r N m : ℕ) (hp : 0 < p) (hr : r < p) (base row : Array ℕ)
    (rows : List (Array ℕ)) (hlen : rows.length = m)
    (hbase : weightedGroupBaseCheck p r 500 N target030Seed373Row14 base = true)
    (hrows : weightedGroupRowsCheck N base row rows = true) :
    row.getD N 0 ≤
      weightedPrimeCount id (List.replicate m p ++ target030Seed373Weights) (r + N * p) := by
  have hsample := weightedGroupBaseCheck_sound p r 500 N target030Seed373Row14 base hbase
  have hb : ∀ k ≤ N, base.getD k 0 ≤ weightedPrimeCount id target030Seed373Weights (r + k * p) := by
    intro k hk
    rw [hsample k hk]
    exact
      (target030Seed373_count_lower (min 500 (r + k * p)) (Nat.min_le_left _ _)).trans
        (weightedPrimeCount_mono id target030Seed373Weights (Nat.min_le_right _ _))
  exact weightedGroupRows_lower p r N m target030Seed373Weights base row rows hp hr hlen hb hrows

/-- A checked short grid combines all numbers of the 209 added labels. Its
base samples the existing count row, and monotonicity covers budgets above
the row's limit of 500. -/
theorem target028_group_grid_lower (r N : ℕ) (hr : r < 76) (base row : Array ℕ)
    (rows : List (Array ℕ)) (hlen : rows.length = 209)
    (hbase : weightedGroupBaseCheck 76 r 500 N target030Seed373Row14 base = true)
    (hrows : weightedGroupRowsCheck N base row rows = true) :
    row.getD N 0 ≤ weightedPrimeCount id target030Seed1849Weights (r + N * 76) := by
  have hsample := weightedGroupBaseCheck_sound 76 r 500 N target030Seed373Row14 base hbase
  have hb :
    ∀ k ≤ N, base.getD k 0 ≤ weightedPrimeCount id target030Seed373Weights (r + k * 76) := by
    intro k hk
    rw [hsample k hk]
    exact
      (target030Seed373_count_lower (min 500 (r + k * 76)) (Nat.min_le_left _ _)).trans
        (weightedPrimeCount_mono id target030Seed373Weights (Nat.min_le_right _ _))
  have hgrid := weightedGroupRowsCheck_sound N base row rows hrows N (le_refl N)
  rw [hlen] at hgrid
  rw [hgrid]
  exact
    weightedGroupGrid_le 76 r target030Seed373Weights (fun k ↦ base.getD k 0) (by decide) hr N hb
      209 N (le_refl N)

end PseudoPrime.PrimeTestBounds.MillerRabin
