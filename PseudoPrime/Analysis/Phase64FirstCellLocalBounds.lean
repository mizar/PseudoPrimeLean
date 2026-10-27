/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.Phase64DyadicLocalBounds
public import PseudoPrime.Analysis.Phase64FirstCellMajorant

/-! # First-cell consumers of the actual dyadic bounds -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- On the certified level cell `64 ≤ L ≤ 64.001`, the ramified dyadic local
cost is at most 427/500 for every finite positive-power prefix. The certified scale
interval lies above 1600, so the continuous estimate applies directly. -/
theorem phase64_first_cell_dyadic_zero_cost_le {f : ℕ} (χ : DirichletCharacter ℂ f) (hχ : χ 2 = 0)
    (K : Finset ℕ) {L : ℝ} (hlo : 64 ≤ L) (hhi : L ≤ 64001 / 1000) :
    finiteSignedActualPrimeLocalCost phaseResolvent64Coefficients χ 2 K (L ^ 2 / (99 / 40)) ≤
      (427 / 500 : ℝ) := by
  exact
    phase64_actual_dyadic_zero_cost_le χ hχ K
      ((by norm_num only : (1600 : ℝ) ≤ 163840 / 99).trans (scale64_cell_of_level hlo hhi).1)

/-- On the certified level cell `64 ≤ L ≤ 64.001`, the minus-one dyadic local
cost after the explicit conductor allowance is at most 473/1000. This connects
the signed Euler and ramp certificate to the same scale as the phase majorant. -/
theorem phase64_first_cell_dyadic_minus_one_cost_le {f : ℕ} (χ : DirichletCharacter ℂ f)
    (hχ : χ 2 = -1) (K : Finset ℕ) {L : ℝ} (hlo : 64 ≤ L) (hhi : L ≤ 64001 / 1000) :
    finiteSignedActualPrimeLocalCost phaseResolvent64Coefficients χ 2 K (L ^ 2 / (99 / 40)) -
        (90992831 / 200000000 : ℝ) * Real.log 4 ≤
      (473 / 1000 : ℝ) := by
  exact
    phase64_actual_dyadic_minus_one_cost_le χ hχ K
      ((by norm_num only : (1600 : ℝ) ≤ 163840 / 99).trans (scale64_cell_of_level hlo hhi).1)

end PseudoPrime.Analysis
