/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.EulerMascheroniBounds
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ReciprocalTrivialZeroSeries
public import PseudoPrime.AnalyticNumberTheory.RiemannXi.ZeroMassBounds

/-! # Numerical lower bound for the reciprocal zeta remainder -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- For x≥2, the reciprocal zeta remainder is at least -32873/20800.
Bound the trivial-zero tail by 1/(18x), the zero-mass contribution by 1/(20sqrt(x)),
and log(2*pi) below by 3/2. Completing a square bounds the remaining quadratic
loss by 9/20800. This improves the constant in reciprocal weighted Mangoldt lower bounds. -/
theorem riemannReciprocalRemainder_lower_bound {x : ℝ} (hx : 2 ≤ x) :
    -(32873 / 20800 : ℝ) ≤
      -(1 + Real.eulerMascheroniConstant) + Real.log (2 * Real.pi) / x -
        riemannReciprocalTrivialZeroSeries x -
        2 * RiemannXi.riemannZeroMass / Real.sqrt x := by
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 2) hx
  have hsqrt : 0 < Real.sqrt x := Real.sqrt_pos.mpr hxpos
  have ht :=
    (riemannReciprocalTrivialZeroSeries_le_geometric hx).trans
      (Analysis.geometricTail_le_one_div_eighteen_mul hx)
  rw [div_mul_eq_div_div] at ht
  have hznum : 2 * RiemannXi.riemannZeroMass ≤ (1 / 20 : ℝ) := by
    linarith only [RiemannXi.riemannZeroMass_le_one_fortieth]
  have hz := (div_le_div_iff_of_pos_right hsqrt).mpr hznum
  have hl := div_le_div_of_nonneg_right Analysis.three_halves_le_log_two_pi hxpos.le
  have hu : (1 / Real.sqrt x) ^ 2 = 1 / x := by rw [div_pow, one_pow, Real.sq_sqrt hxpos.le]
  have hquad :
    -(9 / 20800 : ℝ) ≤ (13 / 9 : ℝ) * (1 / Real.sqrt x) ^ 2 - (1 / 20 : ℝ) * (1 / Real.sqrt x) := by
    nlinarith only [sq_nonneg (1 / Real.sqrt x - (9 / 520 : ℝ))]
  rw [hu, mul_one_div, mul_one_div] at hquad
  have hcost :
    riemannReciprocalTrivialZeroSeries x + 2 * RiemannXi.riemannZeroMass / Real.sqrt x ≤
      (9 / 20800 : ℝ) + Real.log (2 * Real.pi) / x := by
    simp only [div_eq_mul_inv] at ht hz hl hquad ⊢
    nlinarith only [ht, hz, hl, hquad]
  linarith only [hcost, Analysis.eulerMascheroniConstant_lt_twentyNine_fiftieths]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
