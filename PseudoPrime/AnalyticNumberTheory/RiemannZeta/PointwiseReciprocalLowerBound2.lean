/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannXi.FinerLLSConstants

/-! # Pointwise reciprocal losses retaining the scale-dependent terms -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Input: RH, cutoff at least two, and bounds for Euler's constant, zero mass and log(2 pi).
Claim: the reciprocal sum retains its positive inverse-cutoff and negative inverse-root terms.
Proof: bound the trivial-zero tail geometrically before any square completion.
Role: expose cutoff-dependent savings for both witness comparisons. -/
theorem reciprocalWeightedMangoldtSum_ge_pointwise_of_parameters (hRH : RiemannHypothesis)
    {x G B P : ℝ} (hx : 2 ≤ x) (hG : Real.eulerMascheroniConstant ≤ G)
    (hB : RiemannXi.riemannZeroMass ≤ B) (hP : P ≤ Real.log (2 * Real.pi)) :
    Real.log x - (1 + G) - 2 * B / Real.sqrt x + (P - 1 / 18) / x ≤
      Arithmetic.reciprocalWeightedMangoldtSum x := by
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
  have heq := reciprocalWeightedMangoldtSum_eq_integral hxp (τ := 2) (by norm_num only)
  have hre := congrArg Complex.re heq
  rw [Complex.ofReal_re] at hre
  simp only [Complex.ofReal_ofNat] at hre
  rw [hre]
  have hf :=
    re_integral_riemannZetaReciprocalContourKernel_two_ge_of_riemannHypothesis hRH
      (lt_of_lt_of_le (by norm_num only) hx)
  simp only [div_eq_mul_inv] at ht hz hl hf ⊢
  nlinarith only [hf, ht, hz, hl, hG]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
