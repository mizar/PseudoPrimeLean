/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028VariationNumerics
public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleFullPrincipal

/-! # Principal error with sign-split variation constants -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under RH, bound the actual logarithmic Mangoldt error integral through any supported
cutoff using the sharp zero-mass constant and both certified sign-split variation bounds. -/
theorem target028_sharp_integral_bound (hRH : RiemannHypothesis) {x y : ℝ} (hx : 1 ≤ x) (hy : 0 ≤ y)
    (hyb : y ≤ Real.exp (21 / 8 : ℝ)) :
    |∫ u : ℝ in (0 : ℝ)..y,
          (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) - x * u) *
            refinedSecondDensity u| ≤
      (231 / 5000 : ℝ) * Real.sqrt x * ((203 / 1000) * (27 / 25 : ℝ) ^ 5) +
        ((1839 / 1000 : ℝ) * (Real.log x + 21 / 8) + 2) *
          ((251 / 500 : ℝ) * (27 / 25 : ℝ) ^ 5) := by
  let E : ℝ → ℝ := fun u ↦ AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) - x * u
  let D : ℝ := (1839 / 1000 : ℝ) * (Real.log x + 21 / 8) + 2
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hEc : ContinuousOn E (Set.Icc 0 y) :=
    (AnalyticNumberTheory.Arithmetic.continuousOn_logWeightedMangoldtSum_scaled hx0 y).sub
      (continuous_const.mul continuous_id).continuousOn
  have hQ := refined_second_integrable.mono_set (Set.Ioc_subset_Ioc le_rfl hyb)
  have hiE :
    IntervalIntegrable (fun u ↦ E u * refinedSecondDensity u) MeasureTheory.volume 0 y := by
    have hp :=
      MeasureTheory.IntegrableOn.mul_continuousOn_of_subset hQ hEc measurableSet_Ioc isCompact_Icc
        (Set.Ioc_subset_Icc_self : Set.Ioc (0 : ℝ) y ⊆ _)
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hy).mpr
    simpa only [mul_comm] using hp
  have hiF := (intervalIntegrable_iff_integrableOn_Ioc_of_le hy).mp hiE
  have hiAbs :
    MeasureTheory.IntegrableOn (fun u : ℝ ↦ |E u * refinedSecondDensity u|) (Set.Ioc 0 y) := by
    change
      MeasureTheory.Integrable (fun u : ℝ ↦ |E u * refinedSecondDensity u|)
        (MeasureTheory.volume.restrict (Set.Ioc 0 y))
    simpa only [Real.norm_eq_abs] using hiF.norm
  have hsub : Set.Ioc (0 : ℝ) y ⊆ Set.Ioc 0 (Real.exp (21 / 8 : ℝ)) := Set.Ioc_subset_Ioc le_rfl hyb
  have hiV := refined_second_variation.1.mono_set hsub
  have hiN :
    MeasureTheory.IntegrableOn (fun u : ℝ ↦ |refinedSecondDensity u|)
      (Set.Ioc 0 (Real.exp (21 / 8 : ℝ))) := by
    change
      MeasureTheory.Integrable (fun u : ℝ ↦ |refinedSecondDensity u|)
        (MeasureTheory.volume.restrict (Set.Ioc 0 (Real.exp (21 / 8 : ℝ))))
    simpa only [Real.norm_eq_abs] using refined_second_integrable.norm
  have hD : 0 ≤ D := by
    dsimp only [D]; linarith only [Real.log_nonneg hx]
  have hF : 0 ≤ (231 / 5000 : ℝ) * Real.sqrt x := mul_nonneg (by norm_num only) (Real.sqrt_nonneg x)
  have hn :=
    MeasureTheory.norm_integral_le_integral_norm (f := fun u : ℝ ↦ E u * refinedSecondDensity u)
      (μ := MeasureTheory.volume.restrict (Set.Ioc 0 y))
  simp only [Real.norm_eq_abs] at hn
  have hm :
    (∫ u : ℝ in Set.Ioc 0 y, |E u * refinedSecondDensity u|) ≤
      ∫ u : ℝ in Set.Ioc 0 y,
        ((231 / 5000 : ℝ) * Real.sqrt x) * (Real.sqrt u * |refinedSecondDensity u|) +
          D * |refinedSecondDensity u| := by
    apply
      MeasureTheory.integral_mono_ae hiAbs ((hiV.const_mul _).add ((hiN.mono_set hsub).const_mul _))
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with u hu
    have he := refined_scaled_mangoldt_error hRH hx hu.1.le (hu.2.trans hyb)
    have h := mul_le_mul_of_nonneg_right he (abs_nonneg (refinedSecondDensity u))
    dsimp only [E, D, Pi.add_apply]
    rw [abs_mul]
    nlinarith only [h]
  have hV :=
    MeasureTheory.setIntegral_mono_set refined_second_variation.1
      (Filter.Eventually.of_forall
        (fun u : ℝ ↦ mul_nonneg (Real.sqrt_nonneg u) (abs_nonneg (refinedSecondDensity u))))
      (Filter.Eventually.of_forall (fun u hu ↦ hsub hu))
  have hN :=
    MeasureTheory.setIntegral_mono_set hiN
      (Filter.Eventually.of_forall (fun u : ℝ ↦ abs_nonneg (refinedSecondDensity u)))
      (Filter.Eventually.of_forall (fun u hu ↦ hsub hu))
  rw [MeasureTheory.integral_add (hiV.const_mul _) ((hiN.mono_set hsub).const_mul _),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul] at hm
  have hVbound :
    (∫ u : ℝ in Set.Ioc 0 (Real.exp (21 / 8 : ℝ)), Real.sqrt u * |refinedSecondDensity u|) ≤
      (203 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 5 := by
    rw [← intervalIntegral.integral_of_le (Real.exp_pos _).le]
    exact target028_sqrt_variation_bound
  have hNbound :
    (∫ u : ℝ in Set.Ioc 0 (Real.exp (21 / 8 : ℝ)), |refinedSecondDensity u|) ≤
      (251 / 500 : ℝ) * (27 / 25 : ℝ) ^ 5 := by
    rw [← intervalIntegral.integral_of_le (Real.exp_pos _).le]
    exact target028_unweighted_variation_bound
  have h1 := mul_le_mul_of_nonneg_left (hV.trans hVbound) hF
  have h2 := mul_le_mul_of_nonneg_left (hN.trans hNbound) hD
  rw [intervalIntegral.integral_of_le hy]
  dsimp only [D] at h2 hm
  nlinarith only [hn, hm, h1, h2]

/-- Under RH, the finite principal sum differs from its main term by the
sign-split variation allowance and the two retained cutoff endpoint errors.
Divide the sharp integral bound by the positive square root of the scale. -/
theorem target028_principal_sharp_error (hRH : RiemannHypothesis) {x y : ℝ} (hx : 1 ≤ x)
    (hy : 0 ≤ y) (hyb : y ≤ Real.exp (21 / 8 : ℝ)) :
    |(∑ n ∈ Finset.Ioc 0 ⌊x * y⌋₊,
            (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) x n).re) -
          Real.sqrt x * refinedPrincipalMain y| ≤
      ((231 / 5000 : ℝ) * ((203 / 1000) * (27 / 25 : ℝ) ^ 5) +
          ((1839 / 1000 : ℝ) * (Real.log x + 21 / 8) + 2) * ((251 / 500 : ℝ) * (27 / 25 : ℝ) ^ 5) /
            Real.sqrt x) +
        (|y * refinedWeightDeriv y| *
              |AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * y) - x * y| +
            |refinedWeight y| * |Chebyshev.psi (x * y) - x * y|) /
          Real.sqrt x := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hs := (Real.sqrt_pos.mpr hx0).ne'
  apply refined_principal_error_of_integral hx0 hy hyb
  have h := target028_sharp_integral_bound hRH hx hy hyb
  convert h using 1
  field_simp (disch :=
    first
    | exact hs
    | norm_num only)

/-- Under RH, the full principal series differs from the half-point main
term by the two sign-split variation allowances. The endpoint terms vanish
at the support boundary, leaving the improved explicit global estimate. -/
theorem target028_full_principal_error (hRH : RiemannHypothesis) {x : ℝ} (hx : 1 ≤ x) :
    |(∑' n : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) x n).re -
          Real.sqrt x * (refinedSixPoleKernel.function (1 / 2)).re| ≤
      (231 / 5000 : ℝ) * ((203 / 1000) * (27 / 25 : ℝ) ^ 5) +
        ((1839 / 1000 : ℝ) * (Real.log x + 21 / 8) + 2) * ((251 / 500 : ℝ) * (27 / 25 : ℝ) ^ 5) /
          Real.sqrt x := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  rw [refined_full_error_identity hx0, abs_div, abs_of_pos hs]
  apply (div_le_iff₀ hs).mpr
  have h := target028_sharp_integral_bound hRH hx (Real.exp_pos (21 / 8 : ℝ)).le le_rfl
  convert h using 1
  field_simp (disch :=
    first
    | exact hs.ne'
    | norm_num only)

/-- Under RH, the full principal series has an explicit lower bound with the
sharp sign-split variation allowances. This is the principal-side input for
the refined cutoff comparison. -/
theorem target028_full_principal_lower (hRH : RiemannHypothesis) {x : ℝ} (hx : 1 ≤ x) :
    Real.sqrt x * (refinedSixPoleKernel.function (1 / 2)).re -
        ((231 / 5000 : ℝ) * ((203 / 1000) * (27 / 25 : ℝ) ^ 5) +
          ((1839 / 1000 : ℝ) * (Real.log x + 21 / 8) + 2) * ((251 / 500 : ℝ) * (27 / 25 : ℝ) ^ 5) /
            Real.sqrt x) ≤
      (∑' n : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) x n).re := by
  have h := (abs_le.mp (target028_full_principal_error hRH hx)).1
  linarith only [h]

end PseudoPrime.PrimeTestBounds.MillerRabin
