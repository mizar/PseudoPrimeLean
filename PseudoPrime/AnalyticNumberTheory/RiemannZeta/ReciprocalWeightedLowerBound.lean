/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ReciprocalRemainderNumerics
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ReciprocalResidueBoundGeneral
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.WeightedSumIntegral

/-! # Refined RH lower bound for the reciprocal weighted Mangoldt sum -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Under RH and x≥2, the reciprocal weighted Mangoldt sum is at least
log(x)-32873/20800. Transport the reciprocal contour lower bound through the
Mellin identity and apply the numerical remainder estimate. This supplies the
sharper reciprocal input for character comparisons at arbitrary cutoffs. -/
theorem reciprocalWeightedMangoldtSum_lower_bound (hRH : RiemannHypothesis) {x : ℝ} (hx : 2 ≤ x) :
    Real.log x - (32873 / 20800 : ℝ) ≤ Arithmetic.reciprocalWeightedMangoldtSum x := by
  have hx1 : 1 < x := lt_of_lt_of_le (by norm_num only : (1 : ℝ) < 2) hx
  have heq :=
    reciprocalWeightedMangoldtSum_eq_integral (zero_lt_one.trans hx1) (τ := 2) (by norm_num only)
  have hre := congrArg Complex.re heq
  rw [Complex.ofReal_re] at hre
  simp only [Complex.ofReal_ofNat] at hre
  rw [hre]
  have hformula :=
    re_integral_riemannZetaReciprocalContourKernel_two_ge_of_riemannHypothesis hRH hx1
  have hrem := riemannReciprocalRemainder_lower_bound hx
  linarith only [hformula, hrem]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
