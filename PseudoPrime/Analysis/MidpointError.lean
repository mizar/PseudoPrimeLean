/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.MidpointQuadrature

/-! # Midpoint quadrature with a two-sided curvature bound -/

public section

namespace PseudoPrime.Analysis

/-- On an ordered interval, a bound on the absolute second derivative bounds the
midpoint quadrature error by `M * (b - a)^3 / 24`. Apply the lower midpoint
inequality to both the function and its negative. -/
theorem midpoint_integral_error {f f' f'' : ℝ → ℝ} {a b M : ℝ} (hab : a ≤ b)
    (hf : ∀ x ∈ Set.Icc a b, HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Set.Icc a b, HasDerivAt f' (f'' x) x) (hb : ∀ x ∈ Set.Icc a b, |f'' x| ≤ M) :
    |(∫ x in a..b, f x) - (b - a) * f ((a + b) / 2)| ≤ M * (b - a) ^ 3 / 24 := by
  have hlow :=
    midpoint_integral_lower_of_second_deriv_ge hab hf hf' (fun x hx ↦ (abs_le.mp (hb x hx)).1)
  have hupper :=
    midpoint_integral_lower_of_second_deriv_ge hab (fun x hx ↦ (hf x hx).neg)
      (fun x hx ↦ (hf' x hx).neg) (fun x hx ↦ neg_le_neg (abs_le.mp (hb x hx)).2)
  simp only [Pi.neg_apply, intervalIntegral.integral_neg] at hupper
  apply abs_le.mpr
  constructor <;> linarith only [hlow, hupper]

/-- Bound an integral by its midpoint value and a two-sided second-derivative
bound on an ordered interval. This combines the midpoint error estimate with
the supplied bound on the midpoint value. -/
theorem abs_integral_le_midpoint {f f' f'' : ℝ → ℝ} {a b M C : ℝ} (hab : a ≤ b)
    (hf : ∀ x ∈ Set.Icc a b, HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Set.Icc a b, HasDerivAt f' (f'' x) x) (hb : ∀ x ∈ Set.Icc a b, |f'' x| ≤ M)
    (hc : |f ((a + b) / 2)| ≤ C) : |∫ x in a..b, f x| ≤ (b - a) * C + M * (b - a) ^ 3 / 24 := by
  have h := abs_le.mp (midpoint_integral_error hab hf hf' hb)
  have hw : 0 ≤ b - a := sub_nonneg.mpr hab
  have hc1 := mul_le_mul_of_nonneg_left (abs_le.mp hc).1 hw
  have hc2 := mul_le_mul_of_nonneg_left (abs_le.mp hc).2 hw
  apply abs_le.mpr
  constructor <;> nlinarith only [h.1, h.2, hc1, hc2]

end PseudoPrime.Analysis
