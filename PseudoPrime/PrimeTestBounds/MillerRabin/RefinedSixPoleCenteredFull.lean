/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleCenteredBound

/-! # Centered full principal-sum identity -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The full principal series at scale at least one is its kernel main term plus
the centered error integral and the exact logarithmic atom at `1/x`. This form
allows the logarithmic corrections to cancel against the finite unit sum. -/
theorem refined_full_centered_identity {x : ℝ} (hx : 1 ≤ x) :
    (∑' n : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) x n).re -
        Real.sqrt x * (refinedSixPoleKernel.function (1 / 2)).re =
      ((∫ u : ℝ in (0 : ℝ)..Real.exp (21 / 8 : ℝ),
            LLS.clippedShiftError x u * refinedSecondDensity u) -
          Real.log (2 * Real.pi) * refinedWeight (1 / x)) /
        Real.sqrt x := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hv : 0 < 1 / x := one_div_pos.mpr hx0
  have hv1 : 1 / x ≤ 1 := (div_le_iff₀ hx0).mpr (by linarith only [hx])
  have hb : (1 : ℝ) ≤ Real.exp (21 / 8 : ℝ) := Real.one_le_exp_iff.mpr (by norm_num only)
  have hy : (0 : ℝ) ≤ Real.exp (21 / 8 : ℝ) := (Real.exp_pos _).le
  have ha := refined_log_atom hv (hv1.trans hb) le_rfl
  have hc : refinedCoord (Real.exp (21 / 8 : ℝ)) = 0 := by
    norm_num only [refinedCoord, Real.log_exp]
  have hw : refinedWeight (Real.exp (21 / 8 : ℝ)) = 0 := by
    norm_num only [refinedWeight, hc, zero_pow, zero_mul, zero_div]
  have hd : refinedWeightDeriv (Real.exp (21 / 8 : ℝ)) = 0 := by
    norm_num only [refinedWeightDeriv, hc, zero_pow, mul_zero, sub_zero]
  simp only [hw, hd, mul_zero, zero_mul, sub_zero, add_zero] at ha
  have hiA := refined_abel_clipped_integrable hv hy le_rfl
  have hQ := refined_second_integrable
  have hcont :
    ContinuousOn
      (fun u : ℝ ↦ AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) - x * u)
      (Set.Icc 0 (Real.exp (21 / 8 : ℝ))) :=
    (AnalyticNumberTheory.Arithmetic.continuousOn_logWeightedMangoldtSum_scaled hx0 _).sub
      (continuous_const.mul continuous_id).continuousOn
  have hiW :
    IntervalIntegrable
      (fun u : ℝ ↦
        (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) - x * u) *
          refinedSecondDensity u)
      MeasureTheory.volume 0 (Real.exp (21 / 8 : ℝ)) := by
    have h :=
      MeasureTheory.IntegrableOn.mul_continuousOn_of_subset hQ hcont measurableSet_Ioc isCompact_Icc
        (Set.Ioc_subset_Icc_self : Set.Ioc (0 : ℝ) (Real.exp (21 / 8 : ℝ)) ⊆ _)
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hy).mpr
    simpa only [mul_comm] using h
  have hint :
    (∫ u : ℝ in (0 : ℝ)..Real.exp (21 / 8 : ℝ),
        LLS.clippedShiftError x u * refinedSecondDensity u) =
      (∫ u : ℝ in (0 : ℝ)..Real.exp (21 / 8 : ℝ),
          (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) - x * u) *
            refinedSecondDensity u) +
        Real.log (2 * Real.pi) * refinedWeight (1 / x) := by
    rw [ha, ← intervalIntegral.integral_const_mul, ←
      intervalIntegral.integral_add hiW (hiA.const_mul _)]
    congr 1
    funext u
    dsimp only [LLS.clippedShiftError]
    ring
  rw [hint, refined_full_error_identity hx0]
  congr 1
  ring

/-- Subtracting the full principal sum from four unit-cutoff sums combines
the centered error integrals before estimating them. The common logarithmic
atom occurs with coefficient three. -/
theorem refined_combined_centered_identity {x : ℝ} (hx : 1 ≤ x) :
    4 *
          (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
            (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) x n).re) -
        (∑' n : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) x n).re =
      Real.sqrt x * (4 * refinedPrincipalMain 1 - (refinedSixPoleKernel.function (1 / 2)).re) +
        (4 * (∫ u : ℝ in (0 : ℝ)..1, LLS.clippedShiftError x u * refinedSecondDensity u) -
                (∫ u : ℝ in (0 : ℝ)..Real.exp (21 / 8 : ℝ),
                  LLS.clippedShiftError x u * refinedSecondDensity u) -
                4 * refinedWeightDeriv 1 * LLS.clippedShiftError x 1 +
              4 * refinedWeight 1 * (Chebyshev.psi x - x + Real.log (2 * Real.pi)) -
            3 * Real.log (2 * Real.pi) * refinedWeight (1 / x)) /
          Real.sqrt x := by
  have hunit := refined_unit_centered_identity hx
  have hfull := refined_full_centered_identity hx
  ring_nf at hunit hfull ⊢
  linarith only [hunit, hfull]

end PseudoPrime.PrimeTestBounds.MillerRabin
