/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPolePrincipalError
public import PseudoPrime.AnalyticNumberTheory.RiemannXi.FinerLLSConstants2

/-! # Sharp logarithmic Mangoldt error for the refined kernel -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under RH and positive `x`, the logarithmically weighted Mangoldt error is bounded
by `(231/5000) sqrt x + (1839/1000) log(max 1 x) + 2`. Combine the explicit formula
with the certified Riemann zero mass and include the interval below one. -/
theorem refined_log_mangoldt_error (hRH : RiemannHypothesis) {x : ℝ} (hx : 0 < x) :
    |AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum x - x| ≤
      (231 / 5000 : ℝ) * Real.sqrt x + (1839 / 1000 : ℝ) * Real.log (max 1 x) + 2 := by
  by_cases hlarge : 1 < x
  · rw [max_eq_right hlarge.le]
    have hlo := LLS.riemannWeightedLower_of_RH hRH x hlarge
    have he := (abs_le.mp (LLS.abs_logWeightedMangoldtSum_error_le hRH hlarge)).2
    have ht : 0 ≤ AnalyticNumberTheory.RiemannZeta.riemannZetaLogTrivialZeroSeries x := by
      apply tsum_nonneg
      intro k
      exact
        div_nonneg (pow_nonneg (inv_nonneg.mpr (zero_lt_one.trans hlarge).le) _)
          (mul_nonneg (by norm_num only) (sq_nonneg _))
    have hm :=
      mul_le_mul_of_nonneg_right AnalyticNumberTheory.RiemannXi.riemannZeroMass_le_231_div_10000
        (add_nonneg (Real.sqrt_nonneg x) zero_le_one)
    have hl := mul_le_mul_of_nonneg_right Analysis.log_two_mul_pi_lt.le (Real.log_pos hlarge).le
    have hl0 :=
      mul_nonneg (Real.log_nonneg (by nlinarith only [Real.pi_gt_three] : 1 ≤ 2 * Real.pi))
        (Real.log_pos hlarge).le
    rw [abs_le]
    constructor <;>
      nlinarith only [hlo, he, ht, hm, hl, hl0, Real.pi_lt_four, Real.pi_pos,
        sq_nonneg (Real.pi - 4)]
  · have hsmall := le_of_not_gt hlarge
    rw [LLS.logWeightedMangoldtSum_eq_zero_of_le_one hsmall, zero_sub, abs_neg, abs_of_pos hx,
      max_eq_left hsmall, Real.log_one, mul_zero, add_zero]
    linarith only [hsmall, Real.sqrt_nonneg x]

/-- For a scale at least one and a nonnegative point in the kernel support, the
logarithmic Mangoldt error is bounded using the common support endpoint. Apply the sharp
pointwise estimate and monotonicity of the logarithm, including the zero endpoint. -/
theorem refined_scaled_mangoldt_error (hRH : RiemannHypothesis) {x u : ℝ} (hx : 1 ≤ x) (hu : 0 ≤ u)
    (hub : u ≤ Real.exp (21 / 8 : ℝ)) :
    |AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) - x * u| ≤
      (231 / 5000 : ℝ) * Real.sqrt x * Real.sqrt u + (1839 / 1000 : ℝ) * (Real.log x + 21 / 8) +
        2 := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hb : (1 : ℝ) ≤ Real.exp (21 / 8 : ℝ) := Real.one_le_exp_iff.mpr (by norm_num only)
  have hX : 1 ≤ x * Real.exp (21 / 8 : ℝ) := by
    nlinarith only [hx, hb, mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hb)]
  by_cases hu0 : 0 < u
  · have he := refined_log_mangoldt_error hRH (mul_pos hx0 hu0)
    have hmax : max 1 (x * u) ≤ x * Real.exp (21 / 8 : ℝ) :=
      max_le hX (mul_le_mul_of_nonneg_left hub hx0.le)
    have hl := Real.log_le_log (zero_lt_one.trans_le (le_max_left (1 : ℝ) (x * u))) hmax
    rw [Real.log_mul hx0.ne' (Real.exp_pos _).ne', Real.log_exp] at hl
    rw [Real.sqrt_mul hx0.le] at he
    linarith only [he, hl]
  · have heq : u = 0 := le_antisymm (le_of_not_gt hu0) hu
    rw [heq, mul_zero, LLS.logWeightedMangoldtSum_eq_zero_of_le_one (by norm_num only), sub_self,
      abs_zero, Real.sqrt_zero, mul_zero]
    linarith only [Real.log_nonneg hx]

/-- Under RH, bound the actual logarithmic Mangoldt error integral through any supported
cutoff using the sharp zero-mass constant and the second variation. The unweighted
absolute density integral is retained for its separate quantitative evaluation. -/
theorem refined_sharp_integral_bound (hRH : RiemannHypothesis) {x y : ℝ} (hx : 1 ≤ x) (hy : 0 ≤ y)
    (hyb : y ≤ Real.exp (21 / 8 : ℝ)) :
    |∫ u : ℝ in (0 : ℝ)..y,
          (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) - x * u) *
            refinedSecondDensity u| ≤
      (231 / 5000 : ℝ) * Real.sqrt x * (6889 / 2700) +
        ((1839 / 1000 : ℝ) * (Real.log x + 21 / 8) + 2) *
          (∫ u : ℝ in Set.Ioc 0 (Real.exp (21 / 8 : ℝ)), |refinedSecondDensity u|) := by
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
  have h1 := mul_le_mul_of_nonneg_left (hV.trans refined_second_variation.2) hF
  have h2 := mul_le_mul_of_nonneg_left hN hD
  rw [intervalIntegral.integral_of_le hy]
  dsimp only [D] at h2 hm
  nlinarith only [hn, hm, h1, h2]

/-- The unweighted density majorant is integrable on the support and its integral
has the displayed exact exponential value. Evaluate the three coordinate moments. -/
theorem refined_unweighted_majorant_integral :
    MeasureTheory.IntegrableOn refinedSecondMajorant (Set.Ioc 0 (Real.exp (21 / 8 : ℝ))) ∧
      (∫ u : ℝ in Set.Ioc 0 (Real.exp (21 / 8 : ℝ)), refinedSecondMajorant u) =
        (918330048 / 17682025 : ℝ) * Real.exp (-(21 / 16 : ℝ)) := by
  have h3 := refined_density_moment 3 0 (by norm_num only)
  have h4 := refined_density_moment 4 0 (by norm_num only)
  have h5 := refined_density_moment 5 0 (by norm_num only)
  simp only [Real.rpow_zero, one_mul] at h3 h4 h5
  have he :
    refinedSecondMajorant =
      (fun u : ℝ ↦
        (29 / 50 : ℝ) ^ 2 *
            (Real.exp (-refinedCoord u) / (120 * u * Real.sqrt u) * refinedCoord u ^ 5) +
          (10 * (29 / 50 : ℝ) * (27 / 25 : ℝ)) *
            (Real.exp (-refinedCoord u) / (120 * u * Real.sqrt u) * refinedCoord u ^ 4) +
          (20 * (27 / 25 : ℝ) ^ 2) *
            (Real.exp (-refinedCoord u) / (120 * u * Real.sqrt u) * refinedCoord u ^ 3)) := by
    funext u
    dsimp only [refinedSecondMajorant]
    ring
  rw [he]
  have hi5 := h5.1.const_mul ((29 / 50 : ℝ) ^ 2)
  have hi4 := h4.1.const_mul (10 * (29 / 50 : ℝ) * (27 / 25 : ℝ))
  have hi3 := h3.1.const_mul (20 * (27 / 25 : ℝ) ^ 2)
  refine ⟨(hi5.add hi4).add hi3, ?_⟩
  have hsum := MeasureTheory.integral_add (hi5.add hi4) hi3
  have hsum2 := MeasureTheory.integral_add hi5 hi4
  simp only [Pi.add_apply] at hsum hsum2
  rw [hsum, hsum2, MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul, h5.2, h4.2, h3.2]
  norm_num only [Nat.factorial, Nat.reduceAdd, Nat.cast_ofNat]
  have hexp :
    Real.exp (-(567 / 200 : ℝ)) * Real.exp (609 / 400 : ℝ) = Real.exp (-(21 / 16 : ℝ)) := by
    rw [← Real.exp_add]
    norm_num only
  nlinarith only [hexp]

/-- The unweighted absolute second density is bounded by the explicit integral of its
majorant. Apply the pointwise comparison and monotonicity of integration. -/
theorem refined_unweighted_variation :
    (∫ u : ℝ in Set.Ioc 0 (Real.exp (21 / 8 : ℝ)), |refinedSecondDensity u|) ≤
      (918330048 / 17682025 : ℝ) * Real.exp (-(21 / 16 : ℝ)) := by
  have hi :
    MeasureTheory.IntegrableOn (fun u : ℝ ↦ |refinedSecondDensity u|)
      (Set.Ioc 0 (Real.exp (21 / 8 : ℝ))) := by
    change
      MeasureTheory.Integrable (fun u : ℝ ↦ |refinedSecondDensity u|)
        (MeasureTheory.volume.restrict (Set.Ioc 0 (Real.exp (21 / 8 : ℝ))))
    simpa only [Real.norm_eq_abs] using refined_second_integrable.norm
  rw [← refined_unweighted_majorant_integral.2]
  apply MeasureTheory.integral_mono_ae hi refined_unweighted_majorant_integral.1
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with u hu
  have hl : Real.log u ≤ 21 / 8 := (Real.log_le_iff_le_exp hu.1).mpr hu.2
  exact refined_second_abs_le hu.1 hl

/-- Under RH, the logarithmic Mangoldt error integral has a fully explicit upper bound
on the entire kernel support. Insert the evaluated unweighted variation into the sharp
zero-mass estimate; this provides the main integral allowance for the principal sum. -/
theorem refined_sharp_integral_explicit (hRH : RiemannHypothesis) {x y : ℝ} (hx : 1 ≤ x)
    (hy : 0 ≤ y) (hyb : y ≤ Real.exp (21 / 8 : ℝ)) :
    |∫ u : ℝ in (0 : ℝ)..y,
          (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) - x * u) *
            refinedSecondDensity u| ≤
      (231 / 5000 : ℝ) * Real.sqrt x * (6889 / 2700) +
        ((1839 / 1000 : ℝ) * (Real.log x + 21 / 8) + 2) *
          ((918330048 / 17682025 : ℝ) * Real.exp (-(21 / 16 : ℝ))) := by
  have h := refined_sharp_integral_bound hRH hx hy hyb
  have hc : 0 ≤ (1839 / 1000 : ℝ) * (Real.log x + 21 / 8) + 2 := by
    linarith only [Real.log_nonneg hx]
  exact h.trans (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left refined_unweighted_variation hc))

/-- Any bound for the normalized logarithmic Mangoldt error integral transfers to
the finite principal sum while retaining both endpoint errors. Use the exact error identity
and the triangle inequality. -/
theorem refined_principal_error_of_integral {x y K : ℝ} (hx : 0 < x) (hy : 0 ≤ y)
    (hyb : y ≤ Real.exp (21 / 8 : ℝ))
    (hi :
      |∫ u : ℝ in (0 : ℝ)..y,
            (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) - x * u) *
              refinedSecondDensity u| ≤
        K * Real.sqrt x) :
    |(∑ n ∈ Finset.Ioc 0 ⌊x * y⌋₊,
            (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) x n).re) -
          Real.sqrt x * refinedPrincipalMain y| ≤
      K +
        (|y * refinedWeightDeriv y| *
              |AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * y) - x * y| +
            |refinedWeight y| * |Chebyshev.psi (x * y) - x * y|) /
          Real.sqrt x := by
  rw [refined_principal_error_identity hx hy hyb, abs_div, abs_of_nonneg (Real.sqrt_nonneg x)]
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
    _ ≤ (K * Real.sqrt x + |B| + |C|) / Real.sqrt x := by
      apply div_le_div_of_nonneg_right _ hs.le
      change |A| ≤ _ at hi
      linarith only [hi]
    _ = _ := by
      dsimp only [B, C]
      simp only [abs_mul, add_div, mul_div_cancel_right₀ _ hs.ne']
      ring

/-- Under RH, the finite principal error is bounded by the explicit sharp integral
allowance and the two endpoint errors. This applies on every cutoff in the kernel support. -/
theorem refined_principal_sharp_error (hRH : RiemannHypothesis) {x y : ℝ} (hx : 1 ≤ x) (hy : 0 ≤ y)
    (hyb : y ≤ Real.exp (21 / 8 : ℝ)) :
    |(∑ n ∈ Finset.Ioc 0 ⌊x * y⌋₊,
            (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) x n).re) -
          Real.sqrt x * refinedPrincipalMain y| ≤
      ((231 / 5000 : ℝ) * (6889 / 2700) +
          ((1839 / 1000 : ℝ) * (Real.log x + 21 / 8) + 2) *
              ((918330048 / 17682025 : ℝ) * Real.exp (-(21 / 16 : ℝ))) /
            Real.sqrt x) +
        (|y * refinedWeightDeriv y| *
              |AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * y) - x * y| +
            |refinedWeight y| * |Chebyshev.psi (x * y) - x * y|) /
          Real.sqrt x := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hs := (Real.sqrt_pos.mpr hx0).ne'
  apply refined_principal_error_of_integral hx0 hy hyb
  have h := refined_sharp_integral_explicit hRH hx hy hyb
  convert h using 1
  field_simp (disch :=
    first
    | exact hs
    | norm_num only)

end PseudoPrime.PrimeTestBounds.MillerRabin
