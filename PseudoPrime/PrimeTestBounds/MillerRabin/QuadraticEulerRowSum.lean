/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerRowCheck

/-! # Rational scalar aggregation of checked Euler rows -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A rational upper bound on the sum of checked row upper endpoints bounds
the actual Mangoldt sum. Cast the rational list sum and combine row soundness.
This permits one kernel scalar comparison per numerical block. -/
theorem euler_rows_upper_of_rational_sum (rows : List EulerCenterRow) (U : ℚ)
    (hc : rows.all eulerCenterRowCheck = true)
    (hu : (rows.map (fun r ↦ r.hi * Analysis.gammaFiniteEulerUpper r.ratios)).sum ≤ U) :
    (rows.map (fun r ↦ Analysis.gammaResolventMangoldtWeight (r.p ^ (r.k + 1)))).sum ≤ (U : ℝ) := by
  have h := (euler_checked_rows_sum_bounds rows hc).2
  have hR := (Rat.cast_le (K := ℝ)).mpr hu
  simp only [Rat.cast_list_sum, List.map_map, Function.comp_def] at hR
  exact h.trans hR

/-- A rational lower bound on checked row lower endpoints bounds the actual
Mangoldt sum below. Commute the cast with the list sum and apply row soundness.
This supplies finite-prefix lower certificates for the Gamma cells. -/
theorem euler_rows_lower_of_rational_sum (rows : List EulerCenterRow) (L : ℚ)
    (hc : rows.all eulerCenterRowCheck = true)
    (hl : L ≤ (rows.map (fun r ↦ r.lo * Analysis.gammaFiniteEulerLower r.ratios)).sum) :
    (L : ℝ) ≤ (rows.map (fun r ↦ Analysis.gammaResolventMangoldtWeight (r.p ^ (r.k + 1)))).sum := by
  have h := (euler_checked_rows_sum_bounds rows hc).1
  have hR := (Rat.cast_le (K := ℝ)).mpr hl
  simp only [Rat.cast_list_sum, List.map_map, Function.comp_def] at hR
  exact hR.trans h

/-- If checked-row indices are a permutation of an exact support payload,
their actual weighted sums agree. Mapping and summing a list permutation
preserves the Mangoldt contribution. This separates numerical row ordering
from the independently proved prime and higher-power support. -/
theorem euler_rows_sum_of_index_perm (rows : List EulerCenterRow) (pairs : List (ℕ × ℕ))
    (h : (rows.map (fun r ↦ (r.p, r.k))).Perm pairs) :
    (rows.map (fun r ↦ Analysis.gammaResolventMangoldtWeight (r.p ^ (r.k + 1)))).sum =
      (pairs.map (fun pk ↦ Analysis.gammaResolventMangoldtWeight (pk.1 ^ (pk.2 + 1)))).sum := by
  have hs := (h.map (fun pk ↦ Analysis.gammaResolventMangoldtWeight (pk.1 ^ (pk.2 + 1)))).sum_eq
  simpa only [List.map_map, Function.comp_def] using hs

/-- An exact support payload inherits the rational upper bound of checked
rows whose indices permute to it. Transfer the row sum before applying its
certified scalar bound. This connects numerical blocks to actual support data. -/
theorem euler_payload_upper_of_rows (rows : List EulerCenterRow) (pairs : List (ℕ × ℕ)) (U : ℚ)
    (hp : (rows.map (fun r ↦ (r.p, r.k))).Perm pairs) (hc : rows.all eulerCenterRowCheck = true)
    (hu : (rows.map (fun r ↦ r.hi * Analysis.gammaFiniteEulerUpper r.ratios)).sum ≤ U) :
    (pairs.map (fun pk ↦ Analysis.gammaResolventMangoldtWeight (pk.1 ^ (pk.2 + 1)))).sum ≤
      (U : ℝ) := by
  rw [← euler_rows_sum_of_index_perm rows pairs hp]
  exact euler_rows_upper_of_rational_sum rows U hc hu

end PseudoPrime.PrimeTestBounds.MillerRabin
