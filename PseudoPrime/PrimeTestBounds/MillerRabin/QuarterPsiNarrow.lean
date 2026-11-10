/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPolePsiRelativeExact

/-! # Narrow relative window for the quarter bound -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under RH and radius at least 180, the relative-width Chebyshev lower
bound uses `h = (3/7)/sqrt r ≤ 1/30`. This sharper width is used by the
combined centered principal-sum estimate. -/
theorem quarter_psi_narrow (hRH : RiemannHypothesis) {r : ℝ} (hr : 180 ≤ r) :
    let h := (3 / 7 : ℝ) / Real.sqrt r
    (1 - h / (59 / 30)) * r ^ 2 - (231 / 2500 : ℝ) / h * r - (231 / 2500 : ℝ) / h -
        Real.log (2 * Real.pi) ≤
      Chebyshev.psi (r ^ 2) := by
  have hr0 : 0 < r := by linarith only [hr]
  have hs : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr0
  have hs13 : (13 : ℝ) ≤ Real.sqrt r := Real.le_sqrt_of_sq_le (by nlinarith only [hr])
  have hh : 0 < (3 / 7 : ℝ) / Real.sqrt r := div_pos (by norm_num only) hs
  have hw : (3 / 7 : ℝ) / Real.sqrt r ≤ 1 / 30 := by
    apply (div_le_iff₀ hs).mpr
    linarith only [hs13]
  have hz : 1 < (1 - (3 / 7 : ℝ) / Real.sqrt r) * r ^ 2 := by
    have hm :=
      mul_nonneg (show (0 : ℝ) ≤ 1 / 30 - (3 / 7 : ℝ) / Real.sqrt r by linarith only [hw])
        (sq_nonneg r)
    nlinarith only [hr, hm]
  have hp :=
    refined_psi_relative_exact hRH hh hw (by norm_num only : (1 / 30 : ℝ) ≤ 1 / 2) (sq_nonneg r) hz
  norm_num only [Real.sqrt_sq hr0.le] at hp ⊢
  exact hp

end PseudoPrime.PrimeTestBounds.MillerRabin
