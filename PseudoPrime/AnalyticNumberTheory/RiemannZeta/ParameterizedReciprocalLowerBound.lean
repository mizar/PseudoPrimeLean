/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ReciprocalWeightedLowerBound
public import PseudoPrime.AnalyticNumberTheory.RiemannXi.PreciseZeroMassBounds

/-! # Parameterized reciprocal remainder and its precise uniform bound -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For a positive quadratic coefficient a, the expression a*u^2-2*b*u
is bounded below by -b^2/a for all real b,u. Complete a square explicitly.
This keeps the numerical loss parameterized in reciprocal remainder estimates. -/
theorem quadratic_remainder_lower {a b u : ℝ} (ha : 0 < a) :
    -(b ^ 2 / a) ≤ a * u ^ 2 - 2 * b * u := by
  have hid : a * u ^ 2 - 2 * b * u + b ^ 2 / a = a * (u - b / a) ^ 2 := by
    field_simp [ha.ne']
    ring
  have hn := mul_nonneg ha.le (sq_nonneg (u - b / a))
  linarith only [hid, hn]

end PseudoPrime.Analysis

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- For x at least two, upper bounds G,B for the Euler constant and zero
mass and a lower bound P greater than 1/18 for log(2*pi) control the remainder.
Bound the trivial tail geometrically and complete a square in 1/sqrt(x).
This exposes the dependence of the uniform loss on all three analytic inputs. -/
theorem riemannReciprocalRemainder_ge_of_parameters {x G B P : ℝ} (hx : 2 ≤ x)
    (hG : Real.eulerMascheroniConstant ≤ G) (hB : RiemannXi.riemannZeroMass ≤ B)
    (hP : P ≤ Real.log (2 * Real.pi)) (ha : (1 / 18 : ℝ) < P) :
    -(1 + G + B ^ 2 / (P - 1 / 18)) ≤
      -(1 + Real.eulerMascheroniConstant) + Real.log (2 * Real.pi) / x -
        riemannReciprocalTrivialZeroSeries x -
        2 * RiemannXi.riemannZeroMass / Real.sqrt x := by
  have hxp : 0 < x := lt_of_lt_of_le (by norm_num only) hx
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hxp
  have ht :=
    (riemannReciprocalTrivialZeroSeries_le_geometric hx).trans
      (Analysis.geometricTail_le_one_div_eighteen_mul hx)
  rw [div_mul_eq_div_div] at ht
  have hz :=
    (div_le_div_iff_of_pos_right hs).mpr
      (mul_le_mul_of_nonneg_left hB (by norm_num only : (0 : ℝ) ≤ 2))
  have hl := div_le_div_of_nonneg_right hP hxp.le
  have hu : (1 / Real.sqrt x) ^ 2 = 1 / x := by rw [div_pow, one_pow, Real.sq_sqrt hxp.le]
  have hquad :=
    Analysis.quadratic_remainder_lower (a := P - 1 / 18) (b := B) (u := 1 / Real.sqrt x)
      (sub_pos.mpr ha)
  rw [hu] at hquad
  simp only [div_eq_mul_inv] at ht hz hl hquad ⊢
  nlinarith only [ht, hz, hl, hquad, hG]

/-- Under RH and the stated numerical bounds, the reciprocal Mangoldt
sum is at least log x minus the parameterized remainder cost for x at least two.
Transport the contour lower bound through its Mellin identity.
This supplies a reusable arithmetic lower bound for witness comparisons. -/
theorem reciprocalWeightedMangoldtSum_ge_of_parameters (hRH : RiemannHypothesis) {x G B P : ℝ}
    (hx : 2 ≤ x) (hG : Real.eulerMascheroniConstant ≤ G) (hB : RiemannXi.riemannZeroMass ≤ B)
    (hP : P ≤ Real.log (2 * Real.pi)) (ha : (1 / 18 : ℝ) < P) :
    Real.log x - (1 + G + B ^ 2 / (P - 1 / 18)) ≤ Arithmetic.reciprocalWeightedMangoldtSum x := by
  have hx1 : 1 < x := lt_of_lt_of_le (by norm_num only : (1 : ℝ) < 2) hx
  have heq :=
    reciprocalWeightedMangoldtSum_eq_integral (zero_lt_one.trans hx1) (τ := 2) (by norm_num only)
  have hre := congrArg Complex.re heq
  rw [Complex.ofReal_re] at hre
  simp only [Complex.ofReal_ofNat] at hre
  rw [hre]
  have hformula :=
    re_integral_riemannZetaReciprocalContourKernel_two_ge_of_riemannHypothesis hRH hx1
  have hrem := riemannReciprocalRemainder_ge_of_parameters hx hG hB hP ha
  linarith only [hformula, hrem]

/-- Under RH, the reciprocal weighted Mangoldt sum is at least log x minus
789/500 for every x at least two. Instantiate the parameterized remainder with
the certified Euler and Riemann zero-mass bounds. This sharpens the former
8/5 loss without changing the weight or enumerating cutoffs. -/
theorem reciprocalWeightedMangoldtSum_ge_log_sub_789_div_500 (hRH : RiemannHypothesis) {x : ℝ}
    (hx : 2 ≤ x) : Real.log x - (789 / 500 : ℝ) ≤ Arithmetic.reciprocalWeightedMangoldtSum x := by
  have h :=
    reciprocalWeightedMangoldtSum_ge_of_parameters hRH hx
      Analysis.eulerMascheroniConstant_le_5773_div_10000 RiemannXi.riemannZeroMass_le_233_div_10000
      Analysis.log_two_mul_pi_gt.le (by norm_num only : (1 / 18 : ℝ) < 1837 / 1000)
  linarith only [h]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
