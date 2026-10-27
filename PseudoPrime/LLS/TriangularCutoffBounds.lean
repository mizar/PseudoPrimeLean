/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.TriangularCutoffMangoldt
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.TriangularCutoffMainTerm
public import PseudoPrime.LLS.RiemannChebyshevNumericalBounds

/-! # RH error for the alpha-18 finite cutoff sum -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Under RH and positive scale, the finite cutoff Mangoldt sum differs
from its Abel main term by at most 1456 times the scale to power 3/4.
Apply the explicit Chebyshev bound; no further analytic error assumption remains. -/
theorem triangular18_cutoff_mangoldt_error_le_of_rh (hRH : RiemannHypothesis) {x : ℝ} (hx : 0 < x) :
    |(∑ k ∈ Finset.Ioc ⌊Real.exp (-36) * x⌋₊ ⌊x⌋₊,
            ((36 + Real.log ((k : ℝ) / x)) * ((k : ℝ) / x) ^ (-1 / 2 : ℝ)) *
              ArithmeticFunction.vonMangoldt k) -
          (36 * x -
            ∫ t in (Real.exp (-36) * x)..x,
              (((t / x) ^ (-3 / 2 : ℝ) * (1 - (36 + Real.log (t / x)) / 2)) / x) * t)| ≤
      1456 * x ^ (3 / 4 : ℝ) := by
  exact Analysis.triangular18_cutoff_mangoldt_error_le hx (fun t ht ↦ psi_error_le_thirteen hRH ht)

/-- Under RH the finite cutoff sum has explicit main term x(68 + 4 exp(-18))
and lower error 1456 times x to power 3/4. Apply the exact main-term integral
to the finite-sum error bound; this feeds the normalized principal comparison. -/
theorem triangular18_cutoff_mangoldt_lower_of_rh (hRH : RiemannHypothesis) {x : ℝ} (hx : 0 < x) :
    x * (68 + 4 * Real.exp (-18)) - 1456 * x ^ (3 / 4 : ℝ) ≤
      ∑ k ∈ Finset.Ioc ⌊Real.exp (-36) * x⌋₊ ⌊x⌋₊,
        ((36 + Real.log ((k : ℝ) / x)) * ((k : ℝ) / x) ^ (-1 / 2 : ℝ)) *
          ArithmeticFunction.vonMangoldt k := by
  have h := triangular18_cutoff_mangoldt_error_le_of_rh hRH hx
  rw [Analysis.triangular18_cutoff_abel_main_term hx] at h
  have hl := (abs_le.mp h).1
  linarith only [hl]

/-- Under RH the cutoff sum divided by sqrt x is at least the explicit
cutoff mass times sqrt x minus 1456 x^(1/4), for positive scale.
Divide the unnormalized lower bound and simplify the real powers. -/
theorem triangular18_cutoff_mangoldt_normalized_lower_of_rh (hRH : RiemannHypothesis) {x : ℝ}
    (hx : 0 < x) :
    Real.sqrt x * (68 + 4 * Real.exp (-18)) - 1456 * x ^ (1 / 4 : ℝ) ≤
      (∑ k ∈ Finset.Ioc ⌊Real.exp (-36) * x⌋₊ ⌊x⌋₊,
          ((36 + Real.log ((k : ℝ) / x)) * ((k : ℝ) / x) ^ (-1 / 2 : ℝ)) *
            ArithmeticFunction.vonMangoldt k) /
        Real.sqrt x := by
  have hs := Real.sqrt_pos.mpr hx
  have hp : x ^ (3 / 4 : ℝ) / Real.sqrt x = x ^ (1 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_sub hx]
    norm_num only
  have h := div_le_div_of_nonneg_right (triangular18_cutoff_mangoldt_lower_of_rh hRH hx) hs.le
  rw [sub_div, mul_div_assoc 1456, hp] at h
  have he :
    x * (68 + 4 * Real.exp (-18)) / Real.sqrt x = Real.sqrt x * (68 + 4 * Real.exp (-18)) := by
    nth_rw 1 [← Real.sq_sqrt hx.le]
    field_simp [hs.ne']
  simpa only [he] using h

end PseudoPrime.LLS
