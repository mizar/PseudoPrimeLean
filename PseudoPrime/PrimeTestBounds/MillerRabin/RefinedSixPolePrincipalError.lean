/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleSecondVariation
public import PseudoPrime.LLS.RiemannWeightedErrorGlobal
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.ExponentialLogWeightedSummation

/-! # Refined principal sum and logarithmic Mangoldt error -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private theorem refined_density_mul_integrable {f : ℝ → ℝ} {y : ℝ} (hy : 0 ≤ y)
    (hyb : y ≤ Real.exp (21 / 8 : ℝ)) (hf : ContinuousOn f (Set.Icc 0 y)) :
    IntervalIntegrable (fun u : ℝ ↦ f u * refinedSecondDensity u) MeasureTheory.volume 0 y := by
  have hQ := refined_second_integrable.mono_set (Set.Ioc_subset_Ioc le_rfl hyb)
  have hprod :=
    MeasureTheory.IntegrableOn.mul_continuousOn_of_subset hQ hf measurableSet_Ioc isCompact_Icc
      (Set.Ioc_subset_Icc_self : Set.Ioc (0 : ℝ) y ⊆ _)
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hy).mpr
  simpa only [mul_comm] using hprod

/-- Under RH and positive scale, the actual logarithmic Mangoldt error integral
through any supported nonnegative cutoff is at most (6889/1350)*sqrt(x) in absolute value.
Use the global 2*sqrt(t) arithmetic bound and the actual second variation certificate.
This supplies both the unit-cutoff and full-support principal error estimates. -/
theorem refined_error_integral_le (hRH : RiemannHypothesis) {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y)
    (hyb : y ≤ Real.exp (21 / 8 : ℝ)) :
    |∫ u : ℝ in (0 : ℝ)..y,
          (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) - x * u) *
            refinedSecondDensity u| ≤
      (6889 / 1350 : ℝ) * Real.sqrt x := by
  let E : ℝ → ℝ := fun u ↦ AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) - x * u
  have hEc : ContinuousOn E (Set.Icc 0 y) :=
    (AnalyticNumberTheory.Arithmetic.continuousOn_logWeightedMangoldtSum_scaled hx y).sub
      (continuous_const.mul continuous_id).continuousOn
  have hiE := refined_density_mul_integrable hy hyb hEc
  have hiF := (intervalIntegrable_iff_integrableOn_Ioc_of_le hy).mp hiE
  have hiAbs :
    MeasureTheory.IntegrableOn (fun u : ℝ ↦ |E u * refinedSecondDensity u|) (Set.Ioc 0 y) := by
    change
      MeasureTheory.Integrable (fun u : ℝ ↦ |E u * refinedSecondDensity u|)
        (MeasureTheory.volume.restrict (Set.Ioc 0 y))
    simpa only [Real.norm_eq_abs] using hiF.norm
  have hsub : Set.Ioc (0 : ℝ) y ⊆ Set.Ioc 0 (Real.exp (21 / 8 : ℝ)) := Set.Ioc_subset_Ioc le_rfl hyb
  have hiV := refined_second_variation.1.mono_set hsub
  have hiG := hiV.const_mul (2 * Real.sqrt x)
  have hn :=
    MeasureTheory.norm_integral_le_integral_norm (f := fun u : ℝ ↦ E u * refinedSecondDensity u)
      (μ := MeasureTheory.volume.restrict (Set.Ioc 0 y))
  simp only [Real.norm_eq_abs] at hn
  have hm :
    (∫ u : ℝ in Set.Ioc 0 y, |E u * refinedSecondDensity u|) ≤
      ∫ u : ℝ in Set.Ioc 0 y, (2 * Real.sqrt x) * (Real.sqrt u * |refinedSecondDensity u|) := by
    apply MeasureTheory.integral_mono_ae hiAbs hiG
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with u hu
    have he := LLS.mangoldt_log_error_le_two_sqrt hRH (mul_nonneg hx.le hu.1.le)
    rw [Real.sqrt_mul hx.le] at he
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right he (abs_nonneg _)).trans_eq (by ring)
  have hV :=
    MeasureTheory.setIntegral_mono_set refined_second_variation.1
      (Filter.Eventually.of_forall
        (fun u : ℝ ↦ mul_nonneg (Real.sqrt_nonneg u) (abs_nonneg (refinedSecondDensity u))))
      (Filter.Eventually.of_forall (fun u hu ↦ hsub hu))
  have hVbound := hV.trans refined_second_variation.2
  have hscaled :=
    mul_le_mul_of_nonneg_left hVbound
      (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2) (Real.sqrt_nonneg x))
  rw [MeasureTheory.integral_const_mul] at hm
  rw [intervalIntegral.integral_of_le hy]
  exact hn.trans (hm.trans (hscaled.trans_eq (by ring)))

/-- Split the actual logarithmic Mangoldt integral into its linear main term
and genuine arithmetic error. Continuity times the integrable density justifies
subtraction and the scale factor. This preserves the exact normalization in both sums. -/
theorem refined_log_integral_split {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y)
    (hyb : y ≤ Real.exp (21 / 8 : ℝ)) :
    (∫ u : ℝ in (0 : ℝ)..y,
        AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) * refinedSecondDensity u) =
      x * (∫ u : ℝ in (0 : ℝ)..y, u * refinedSecondDensity u) +
        ∫ u : ℝ in (0 : ℝ)..y,
          (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) - x * u) *
            refinedSecondDensity u := by
  have hiM :=
    refined_density_mul_integrable hy hyb
      (AnalyticNumberTheory.Arithmetic.continuousOn_logWeightedMangoldtSum_scaled hx y)
  have hiL :=
    refined_density_mul_integrable (f := fun u : ℝ ↦ x * u) hy hyb
      (continuous_const.mul continuous_id).continuousOn
  have h := intervalIntegral.integral_sub hiM hiL
  have he :
    (fun u : ℝ ↦
        AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) * refinedSecondDensity u -
          (x * u) * refinedSecondDensity u) =
      (fun u : ℝ ↦
        (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) - x * u) *
          refinedSecondDensity u) := by
    funext u
    ring
  rw [he] at h
  simp only [mul_assoc, intervalIntegral.integral_const_mul] at h
  linarith only [h]

/-- The finite-cutoff main coefficient reconstructed from the second Abel density and
both endpoint terms. Multiplication by the square root of the scale gives the main term. -/
noncomputable def refinedPrincipalMain (y : ℝ) : ℝ :=
  (∫ u : ℝ in (0 : ℝ)..y, u * refinedSecondDensity u) - y ^ 2 * refinedWeightDeriv y +
    y * refinedWeight y

/-- At positive scale and a cutoff within support, the principal sum minus its main term
is exactly the logarithmic Mangoldt error integral and both endpoint errors, normalized by
the square root of the scale. Split the double Abel integral and rearrange the terms. -/
theorem refined_principal_error_identity {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y)
    (hyb : y ≤ Real.exp (21 / 8 : ℝ)) :
    (∑ n ∈ Finset.Ioc 0 ⌊x * y⌋₊,
          (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) x n).re) -
        Real.sqrt x * refinedPrincipalMain y =
      ((∫ u : ℝ in (0 : ℝ)..y,
              (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) - x * u) *
                refinedSecondDensity u) -
            y * refinedWeightDeriv y *
              (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * y) - x * y) +
          refinedWeight y * (Chebyshev.psi (x * y) - x * y)) /
        Real.sqrt x := by
  rw [refined_principal_double_abel hx hy hyb, refined_log_integral_split hx hy hyb]
  dsimp only [refinedPrincipalMain]
  have hs := (Real.sqrt_pos.mpr hx).ne'
  field_simp (disch :=
    first
    | exact hs
    | norm_num only)
  rw [Real.sq_sqrt hx.le]
  ring

/-- Under RH, the principal error has an explicit integral allowance `6889/1350`
plus the actual two endpoint errors. Apply the global logarithmic Mangoldt error and the
second-density variation, retaining endpoint terms for sharper cutoff estimates. -/
theorem refined_principal_error_bound (hRH : RiemannHypothesis) {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y)
    (hyb : y ≤ Real.exp (21 / 8 : ℝ)) :
    |(∑ n ∈ Finset.Ioc 0 ⌊x * y⌋₊,
            (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) x n).re) -
          Real.sqrt x * refinedPrincipalMain y| ≤
      (6889 / 1350 : ℝ) +
        (|y * refinedWeightDeriv y| *
              |AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * y) - x * y| +
            |refinedWeight y| * |Chebyshev.psi (x * y) - x * y|) /
          Real.sqrt x := by
  rw [refined_principal_error_identity hx hy hyb, abs_div, abs_of_nonneg (Real.sqrt_nonneg x)]
  have hi := refined_error_integral_le hRH hx hy hyb
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  let A : ℝ :=
    ∫ u : ℝ in (0 : ℝ)..y,
      (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) - x * u) *
        refinedSecondDensity u
  let B : ℝ :=
    y * refinedWeightDeriv y *
      (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * y) - x * y)
  let C : ℝ := refinedWeight y * (Chebyshev.psi (x * y) - x * y)
  have ht := abs_add_le (A - B) C
  have ht2 : |A - B| ≤ |A| + |B| := by
    simpa only [sub_eq_add_neg, abs_neg] using (abs_add_le A (-B))
  have htri : |A - B + C| ≤ |A| + |B| + |C| := by linarith only [ht, ht2]
  change |A - B + C| / Real.sqrt x ≤ _
  calc
    _ ≤ (|A| + |B| + |C|) / Real.sqrt x := div_le_div_of_nonneg_right htri hs.le
    _ ≤ ((6889 / 1350 : ℝ) * Real.sqrt x + |B| + |C|) / Real.sqrt x := by
      apply div_le_div_of_nonneg_right _ hs.le
      change |A| ≤ _ at hi
      linarith only [hi]
    _ = _ := by
      dsimp only [B, C]
      simp only [abs_mul, add_div, mul_div_cancel_right₀ _ hs.ne']
      ring

end PseudoPrime.PrimeTestBounds.MillerRabin
