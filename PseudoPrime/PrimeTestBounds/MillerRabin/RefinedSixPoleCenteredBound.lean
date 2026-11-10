/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleCenteredPrincipal
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028SharpPrincipal

/-! # Centered error integral for the refined principal sum -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under RH, the centered logarithmic Mangoldt error integral is bounded by
the square-root and unweighted variations of the six-pole kernel. The bound
applies to every cutoff in the support and has no logarithmic loss. -/
theorem refined_centered_integral_bound (hRH : RiemannHypothesis) {x y : ℝ} (hx : 1 ≤ x)
    (hy : 0 ≤ y) (hyb : y ≤ Real.exp (21 / 8 : ℝ)) :
    |∫ u : ℝ in (0 : ℝ)..y, LLS.clippedShiftError x u * refinedSecondDensity u| ≤
      (1 / 20 : ℝ) * Real.sqrt x * ((203 / 1000) * (27 / 25 : ℝ) ^ 5) +
        (21 / 20 : ℝ) * ((251 / 500) * (27 / 25 : ℝ) ^ 5) := by
  let E : ℝ → ℝ := LLS.clippedShiftError x
  let D : ℝ := (21 / 20 : ℝ)
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hEc : ContinuousOn E (Set.Icc 0 y) := LLS.clippedShiftError_continuousOn hx0 y
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
    dsimp only [D]; norm_num only
  have hF : 0 ≤ (1 / 20 : ℝ) * Real.sqrt x := mul_nonneg (by norm_num only) (Real.sqrt_nonneg x)
  have hn :=
    MeasureTheory.norm_integral_le_integral_norm (f := fun u : ℝ ↦ E u * refinedSecondDensity u)
      (μ := MeasureTheory.volume.restrict (Set.Ioc 0 y))
  simp only [Real.norm_eq_abs] at hn
  have hm :
    (∫ u : ℝ in Set.Ioc 0 y, |E u * refinedSecondDensity u|) ≤
      ∫ u : ℝ in Set.Ioc 0 y,
        ((1 / 20 : ℝ) * Real.sqrt x) * (Real.sqrt u * |refinedSecondDensity u|) +
          D * |refinedSecondDensity u| := by
    apply
      MeasureTheory.integral_mono_ae hiAbs ((hiV.const_mul _).add ((hiN.mono_set hsub).const_mul _))
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with u hu
    have he := LLS.clippedShiftError_abs_le hRH hx0 hu.1.le
    rw [Real.sqrt_mul hx0.le] at he
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

end PseudoPrime.PrimeTestBounds.MillerRabin
