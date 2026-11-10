/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleCenteredNumerics
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentMonotone

/-! # The inverse-scale principal weight -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The inverse-scale weight appearing in the centered comparison. It is the
explicit conductor factor at the square scale `r²`. -/
noncomputable def quarterReflectedScale (r : ℝ) : ℝ :=
  ((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8))) * (r ^ 2) ^ (-(27 / 25 : ℝ)) *
    ((21 / 8 : ℝ) + Real.log (r ^ 2)) ^ 5

/-- For positive `r`, the centered logarithmic atom equals the explicit
conductor factor. Expand the inverse weight and simplify its square root. -/
theorem quarter_reflected_scale_eq {r : ℝ} (hr : 0 < r) :
    refinedWeight (1 / r ^ 2) / r = quarterReflectedScale r := by
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  have hc : refinedCoord (1 / r ^ 2) = (27 / 25 : ℝ) * ((21 / 8 : ℝ) + Real.log (r ^ 2)) := by
    dsimp only [refinedCoord]
    rw [Real.log_div (by norm_num only : (1 : ℝ) ≠ 0) hr2.ne', Real.log_one]
    ring
  have he :
    Real.exp (-((27 / 25 : ℝ) * ((21 / 8 : ℝ) + Real.log (r ^ 2)))) =
      Real.exp (-((27 / 25 : ℝ) * (21 / 8))) * (r ^ 2) ^ (-(27 / 25 : ℝ)) := by
    rw [Real.rpow_def_of_pos hr2, ← Real.exp_add]
    congr 1
    ring
  have hs : Real.sqrt (1 / r ^ 2) = 1 / r := by
    rw [one_div, Real.sqrt_inv, Real.sqrt_sq hr.le, ← one_div]
  dsimp only [refinedWeight, quarterReflectedScale]
  rw [hc, he, hs]
  field_simp (disch :=
    first
    | exact hr.ne'
    | norm_num only)

end PseudoPrime.PrimeTestBounds.MillerRabin
