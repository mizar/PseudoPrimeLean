/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev

/-! # Shared analytic conclusions of the two theta guards -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

/-- A psi bound at coefficient `c` and the direct theta lower guard at
coefficient `t ≥ c` give the two-sided theta bound, using theta ≤ psi. -/
theorem theta_abs_of_lower {x c t : ℝ} (hc : c ≤ t) (hp : |Chebyshev.psi x - x| ≤ c * Real.sqrt x)
    (hl : x - Chebyshev.theta x ≤ t * Real.sqrt x) : |Chebyshev.theta x - x| ≤ t * Real.sqrt x := by
  have hu := (sub_le_sub_right (Chebyshev.theta_le_psi x) x).trans (abs_le.mp hp).2
  exact
    abs_le.mpr
      ⟨by linarith only [hl], hu.trans (mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg x))⟩

/-- When higher prime powers contribute at most the gap between coefficients,
the psi bound supplies the theta lower guard and hence the full theta bound. -/
theorem theta_abs_of_defect {x c t : ℝ} (hc : c ≤ t) (hp : |Chebyshev.psi x - x| ≤ c * Real.sqrt x)
    (hd : Chebyshev.psi x - Chebyshev.theta x ≤ (t - c) * Real.sqrt x) :
    |Chebyshev.theta x - x| ≤ t * Real.sqrt x := by
  apply theta_abs_of_lower hc hp
  rw [sub_mul] at hd
  linarith only [(abs_le.mp hp).1, hd]

/-- A nonnegative constant lower tick bound at the right crossing suffices
throughout a cell. When the coefficient exceeds the local square root the
conclusion follows from nonnegativity alone. -/
theorem lower_on_cell {x b l c : ℝ} (hx : 0 ≤ x) (hxb : x ≤ b) (hl : 0 ≤ l)
    (hb : b - l ≤ c * Real.sqrt b) : x - l ≤ c * Real.sqrt x := by
  by_cases h : c ≤ Real.sqrt x
  · have hm :=
      mul_le_mul (Real.sqrt_le_sqrt hxb) (sub_le_sub_right (Real.sqrt_le_sqrt hxb) c)
        (sub_nonneg.mpr h) (Real.sqrt_nonneg b)
    nlinarith only [hm, Real.sq_sqrt hx, Real.sq_sqrt (hx.trans hxb), hb]
  · have hm := mul_le_mul_of_nonneg_right (le_of_not_ge h) (Real.sqrt_nonneg x)
    nlinarith only [hm, Real.sq_sqrt hx, hl]

/-- A certified constant lower estimate for theta and a right-end crossing,
together with the psi bound, imply the theta estimate anywhere in the cell. -/
theorem theta_abs_on_cell {x b l c t : ℝ} (hx : 0 ≤ x) (hxb : x ≤ b) (hl : 0 ≤ l)
    (ht : l ≤ Chebyshev.theta x) (hc : c ≤ t) (hp : |Chebyshev.psi x - x| ≤ c * Real.sqrt x)
    (hb : b - l ≤ t * Real.sqrt b) : |Chebyshev.theta x - x| ≤ t * Real.sqrt x := by
  exact theta_abs_of_lower hc hp ((sub_le_sub_left ht x).trans (lower_on_cell hx hxb hl hb))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
