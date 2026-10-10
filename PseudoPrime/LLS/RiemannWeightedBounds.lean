/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LogResidueBoundGeneral
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ReciprocalResidueBoundGeneral
public import PseudoPrime.LLS.ExplicitFormula

/-!
# RH-conditional Riemann weighted-sum bounds

The Mellin identities at real part two transport the RH-conditional logarithmic and reciprocal
contour bounds to the finite weighted Mangoldt sums used in LLS. The reciprocal estimate also
uses the numerical remainder bound to obtain log x - 8/5 for x ≥ 2.
-/

@[expose] public section

namespace PseudoPrime.LLS

open PseudoPrime.AnalyticNumberTheory.RiemannZeta in
/-- Under RH, the logarithmic weighted Mangoldt sum satisfies LLS Lemma 2.1 for
x > 1. The Mellin identity at real part two transports the contour lower bound
directly to the finite sum, supplying the Riemann input for LLS Theorem 1.1. -/
theorem llsRiemannWeightedLowerBound_of_riemannHypothesis (hRH : RiemannHypothesis) :
    LLSRiemannWeightedLowerBound := by
  intro x hx
  have heq := logWeightedMangoldtSum_eq_integral (zero_lt_one.trans hx) (τ := 2) (by norm_num only)
  have hre := congrArg Complex.re heq
  rw [Complex.ofReal_re] at hre
  rw [hre]
  exact re_integral_riemannZetaLogContourKernel_two_ge_of_riemannHypothesis hRH hx

open PseudoPrime.AnalyticNumberTheory.RiemannZeta in
/-- Under RH, the reciprocal weighted Mangoldt sum is at least log x - 8/5
for x ≥ 2. The Mellin identity at real part two gives the explicit lower bound;
the numerical remainder estimate yields the input used in LLS Section 3.1. -/
theorem llsRiemannReciprocalLowerBound_of_riemannHypothesis (hRH : RiemannHypothesis) :
    LLSRiemannReciprocalLowerBound := by
  apply llsRiemannReciprocalLowerBound_of_explicit_analytic
  intro x hx
  have heq :=
    reciprocalWeightedMangoldtSum_eq_integral (zero_lt_one.trans hx) (τ := 2) (by norm_num only)
  have hre := congrArg Complex.re heq
  rw [Complex.ofReal_re] at hre
  rw [hre]
  exact re_integral_riemannZetaReciprocalContourKernel_two_ge_of_riemannHypothesis hRH hx

end PseudoPrime.LLS
