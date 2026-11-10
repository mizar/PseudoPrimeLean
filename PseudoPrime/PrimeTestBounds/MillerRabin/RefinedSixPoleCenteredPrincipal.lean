/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPolePrincipalError
public import PseudoPrime.LLS.ClippedLogShiftPrincipalBounds

/-! # Centered double Abel identity at the unit cutoff -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Centering the logarithmic Mangoldt error retains the exact logarithmic atom.
At scale `x ≥ 1`, the unit-cutoff finite principal sum is given by the centered
error integral, its boundary values and the weight at `1/x`. This identity is
the starting point for the joint finite/full principal-sum estimate. -/
theorem refined_unit_centered_identity {x : ℝ} (hx : 1 ≤ x) :
    (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) x n).re) -
        Real.sqrt x * refinedPrincipalMain 1 =
      ((∫ u : ℝ in (0 : ℝ)..1, LLS.clippedShiftError x u * refinedSecondDensity u) -
              refinedWeightDeriv 1 * LLS.clippedShiftError x 1 +
            refinedWeight 1 * (Chebyshev.psi x - x + Real.log (2 * Real.pi)) -
          Real.log (2 * Real.pi) * refinedWeight (1 / x)) /
        Real.sqrt x := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hv : 0 < 1 / x := one_div_pos.mpr hx0
  have hv1 : 1 / x ≤ 1 := (div_le_iff₀ hx0).mpr (by linarith only [hx])
  have hb : (1 : ℝ) ≤ Real.exp (21 / 8 : ℝ) := Real.one_le_exp_iff.mpr (by norm_num only)
  have ha := refined_log_atom hv hv1 hb
  have hiA := refined_abel_clipped_integrable hv (by norm_num only) hb
  have hQ := refined_second_integrable.mono_set (Set.Ioc_subset_Ioc le_rfl hb)
  have hc :
    ContinuousOn
      (fun u : ℝ ↦ AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) - x * u)
      (Set.Icc 0 1) :=
    (AnalyticNumberTheory.Arithmetic.continuousOn_logWeightedMangoldtSum_scaled hx0 1).sub
      (continuous_const.mul continuous_id).continuousOn
  have hiW :
    IntervalIntegrable
      (fun u : ℝ ↦
        (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) - x * u) *
          refinedSecondDensity u)
      MeasureTheory.volume 0 1 := by
    have h :=
      MeasureTheory.IntegrableOn.mul_continuousOn_of_subset hQ hc measurableSet_Ioc isCompact_Icc
        (Set.Ioc_subset_Icc_self : Set.Ioc (0 : ℝ) 1 ⊆ _)
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num only)).mpr
    simpa only [mul_comm] using h
  have hint :
    (∫ u : ℝ in (0 : ℝ)..1, LLS.clippedShiftError x u * refinedSecondDensity u) =
      (∫ u : ℝ in (0 : ℝ)..1,
          (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) - x * u) *
            refinedSecondDensity u) +
        Real.log (2 * Real.pi) *
          (∫ u : ℝ in (0 : ℝ)..1,
            Analysis.positiveLogRatio (1 / x) u * refinedSecondDensity u) := by
    rw [← intervalIntegral.integral_const_mul, ←
      intervalIntegral.integral_add hiW (hiA.const_mul _)]
    congr 1
    funext u
    dsimp only [LLS.clippedShiftError]
    ring
  have hend :
    LLS.clippedShiftError x 1 =
      AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum x - x +
        Real.log (2 * Real.pi) * Real.log x := by
    dsimp only [LLS.clippedShiftError]
    rw [LLS.clippedLogAtom_eq_log_max hx0, mul_one, max_eq_right hx]
  have heq := refined_principal_error_identity hx0 (by norm_num only : (0 : ℝ) ≤ 1) hb
  simp only [mul_one, one_mul] at heq
  rw [hint, hend, heq]
  have ha' := congrArg (fun z : ℝ ↦ Real.log (2 * Real.pi) * z) ha
  simp only [one_mul, one_div, inv_inv] at ha'
  congr 1
  ring_nf at ha' ⊢
  linarith only [ha']

end PseudoPrime.PrimeTestBounds.MillerRabin
