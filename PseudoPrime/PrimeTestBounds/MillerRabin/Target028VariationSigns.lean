/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleSecondVariation

/-! # Sign intervals for the refined second variation -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The quadratic governing the second variation factors at `5 ± sqrt 5`.
This exact identity supplies the sign split for the absolute integral. -/
theorem target028_variation_quadratic_factor (x : ℝ) :
    x ^ 2 - 10 * x + 20 = (x - (5 - Real.sqrt 5)) * (x - (5 + Real.sqrt 5)) := by
  have hs : (Real.sqrt 5) ^ 2 = (5 : ℝ) := Real.sq_sqrt (by norm_num only)
  nlinarith only [hs]

/-- The variation quadratic is nonnegative outside its two roots. The factor
signs select the two positive pieces of the absolute variation integral. -/
theorem target028_variation_quadratic_nonneg {x : ℝ}
    (h : x ≤ 5 - Real.sqrt 5 ∨ 5 + Real.sqrt 5 ≤ x) : 0 ≤ x ^ 2 - 10 * x + 20 := by
  rw [target028_variation_quadratic_factor]
  rcases h with h | h
  · exact
      mul_nonneg_of_nonpos_of_nonpos (by linarith only [h])
        (by linarith only [h, Real.sqrt_nonneg 5])
  · exact mul_nonneg (by linarith only [h, Real.sqrt_nonneg 5]) (by linarith only [h])

/-- The variation quadratic is nonpositive between its two roots. This is
the negative piece that must be subtracted when evaluating the absolute integral. -/
theorem target028_variation_quadratic_nonpos {x : ℝ} (hlo : 5 - Real.sqrt 5 ≤ x)
    (hhi : x ≤ 5 + Real.sqrt 5) : x ^ 2 - 10 * x + 20 ≤ 0 := by
  rw [target028_variation_quadratic_factor]
  exact mul_nonpos_of_nonneg_of_nonpos (by linarith only [hlo]) (by linarith only [hhi])

/-- On the positive support, the refined second density is a nonnegative
factor times the variation quadratic at `(29/54) * refinedCoord u`. This
factorization connects the scalar sign split to the double-Abel density. -/
theorem target028_density_factor (u : ℝ) :
    refinedSecondDensity u =
      (Real.exp (-refinedCoord u) / (120 * u * Real.sqrt u) * (27 / 25 : ℝ) ^ 2 *
          refinedCoord u ^ 3) *
        (((29 / 54 : ℝ) * refinedCoord u) ^ 2 - 10 * ((29 / 54 : ℝ) * refinedCoord u) + 20) := by
  dsimp only [refinedSecondDensity]
  ring

/-- The prefactor in the density factorization is nonnegative for positive
arguments inside the logarithmic support. -/
theorem target028_density_prefactor_nonneg {u : ℝ} (hu : 0 < u) (hl : Real.log u ≤ 21 / 8) :
    0 ≤
      Real.exp (-refinedCoord u) / (120 * u * Real.sqrt u) * (27 / 25 : ℝ) ^ 2 *
        refinedCoord u ^ 3 := by
  have hv : 0 ≤ refinedCoord u := by
    dsimp only [refinedCoord]
    linarith only [hl]
  exact
    mul_nonneg
      (mul_nonneg
        (div_nonneg (Real.exp_nonneg _)
          (mul_nonneg (mul_nonneg (by norm_num only) hu.le) (Real.sqrt_nonneg _)))
        (sq_nonneg _))
      (pow_nonneg hv _)

/-- On the positive support, the second density is nonnegative when the
scaled coordinate lies outside the two variation roots. -/
theorem target028_density_nonneg {u : ℝ} (hu : 0 < u) (hl : Real.log u ≤ 21 / 8)
    (h :
      (29 / 54 : ℝ) * refinedCoord u ≤ 5 - Real.sqrt 5 ∨
        5 + Real.sqrt 5 ≤ (29 / 54 : ℝ) * refinedCoord u) :
    0 ≤ refinedSecondDensity u := by
  rw [target028_density_factor]
  exact
    mul_nonneg (target028_density_prefactor_nonneg hu hl) (target028_variation_quadratic_nonneg h)

/-- On the positive support, the second density is nonpositive when the
scaled coordinate lies between the variation roots. -/
theorem target028_density_nonpos {u : ℝ} (hu : 0 < u) (hl : Real.log u ≤ 21 / 8)
    (hlo : 5 - Real.sqrt 5 ≤ (29 / 54 : ℝ) * refinedCoord u)
    (hhi : (29 / 54 : ℝ) * refinedCoord u ≤ 5 + Real.sqrt 5) : refinedSecondDensity u ≤ 0 := by
  rw [target028_density_factor]
  exact
    mul_nonpos_of_nonneg_of_nonpos (target028_density_prefactor_nonneg hu hl)
      (target028_variation_quadratic_nonpos hlo hhi)

/-- The lower support point corresponding to the larger quadratic root. -/
noncomputable def target028VariationLower : ℝ :=
  Real.exp (21 / 8 - (50 / 29) * (5 + Real.sqrt 5))

/-- The upper support point corresponding to the smaller quadratic root. -/
noncomputable def target028VariationUpper : ℝ :=
  Real.exp (21 / 8 - (50 / 29) * (5 - Real.sqrt 5))

/-- The refined second density is nonpositive between the two support points.
Monotonicity of the logarithm transfers the exact scalar root conditions to
the integration variable. -/
theorem target028_density_middle {u : ℝ} (hlo : target028VariationLower ≤ u)
    (hhi : u ≤ target028VariationUpper) : refinedSecondDensity u ≤ 0 := by
  have hlowpos : 0 < target028VariationLower := Real.exp_pos _
  have hu : 0 < u := hlowpos.trans_le hlo
  have hl := Real.log_le_log hlowpos hlo
  have hh := Real.log_le_log hu hhi
  dsimp only [target028VariationLower] at hl
  dsimp only [target028VariationUpper] at hh
  rw [Real.log_exp] at hl hh
  have hs : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg _
  have hs2 : (Real.sqrt 5) ^ 2 = (5 : ℝ) := Real.sq_sqrt (by norm_num only)
  have hroot : Real.sqrt 5 ≤ 5 := by nlinarith only [hs, hs2]
  have hsupport : Real.log u ≤ 21 / 8 := by linarith only [hh, hroot]
  apply target028_density_nonpos hu hsupport
  · dsimp only [refinedCoord]
    linarith only [hh]
  · dsimp only [refinedCoord]
    linarith only [hl]

/-- The refined second density is nonnegative below the lower support point.
The logarithmic coordinate then lies above the larger quadratic root. -/
theorem target028_density_lower {u : ℝ} (hu : 0 < u) (h : u ≤ target028VariationLower) :
    0 ≤ refinedSecondDensity u := by
  have hl := Real.log_le_log hu h
  dsimp only [target028VariationLower] at hl
  rw [Real.log_exp] at hl
  have hs : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg _
  have hsupport : Real.log u ≤ 21 / 8 := by linarith only [hl, hs]
  apply target028_density_nonneg hu hsupport
  right
  dsimp only [refinedCoord]
  linarith only [hl]

/-- The refined second density is nonnegative between the upper support
point and the endpoint of the support. The coordinate lies below the smaller
quadratic root throughout this interval. -/
theorem target028_density_upper {u : ℝ} (h : target028VariationUpper ≤ u)
    (hsupport : Real.log u ≤ 21 / 8) : 0 ≤ refinedSecondDensity u := by
  have hup : 0 < target028VariationUpper := Real.exp_pos _
  have hu : 0 < u := hup.trans_le h
  have hl := Real.log_le_log hup h
  dsimp only [target028VariationUpper] at hl
  rw [Real.log_exp] at hl
  apply target028_density_nonneg hu hsupport
  left
  dsimp only [refinedCoord]
  linarith only [hl]

/-- The two sign-change points are positive, ordered, and lie in the support.
The inequalities allow the absolute variation to be split into three integrals. -/
theorem target028_variation_points_ordered :
    0 < target028VariationLower ∧
      target028VariationLower ≤ target028VariationUpper ∧
      target028VariationUpper ≤ Real.exp (21 / 8 : ℝ) := by
  have hs : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg _
  have hs2 : (Real.sqrt 5) ^ 2 = (5 : ℝ) := Real.sq_sqrt (by norm_num only)
  have hroot : Real.sqrt 5 ≤ 5 := by nlinarith only [hs, hs2]
  refine ⟨Real.exp_pos _, ?_, ?_⟩
  · apply Real.exp_le_exp.mpr
    linarith only [hs]
  · apply Real.exp_le_exp.mpr
    linarith only [hroot]

/-- The absolute second variation is the sum of the two outer signed
integrals minus the middle integral. The established sign intervals justify
each replacement without discarding cancellation. -/
theorem target028_variation_signed_split :
    (∫ u : ℝ in (0 : ℝ)..Real.exp (21 / 8 : ℝ), |refinedSecondDensity u|) =
      (∫ u : ℝ in (0 : ℝ)..target028VariationLower, refinedSecondDensity u) -
          (∫ u : ℝ in target028VariationLower..target028VariationUpper, refinedSecondDensity u) +
        ∫ u : ℝ in target028VariationUpper..Real.exp (21 / 8 : ℝ), refinedSecondDensity u := by
  have hord := target028_variation_points_ordered
  have h0l : (0 : ℝ) ≤ target028VariationLower := hord.1.le
  have hlu := hord.2.1
  have hue := hord.2.2
  have h0u := h0l.trans hlu
  have h0e := h0u.trans hue
  have hI :
    IntervalIntegrable (fun u : ℝ ↦ |refinedSecondDensity u|) MeasureTheory.volume 0
      (Real.exp (21 / 8 : ℝ)) := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le h0e).mpr
    change
      MeasureTheory.Integrable (fun u : ℝ ↦ |refinedSecondDensity u|)
        (MeasureTheory.volume.restrict (Set.Ioc 0 (Real.exp (21 / 8 : ℝ))))
    simpa only [Real.norm_eq_abs] using refined_second_integrable.norm
  have hIL :
    IntervalIntegrable (fun u : ℝ ↦ |refinedSecondDensity u|) MeasureTheory.volume 0
      target028VariationLower := by
    apply hI.mono_set
    rw [Set.uIcc_of_le h0e, Set.uIcc_of_le h0l]
    exact Set.Icc_subset_Icc_right (hlu.trans hue)
  have hIM :
    IntervalIntegrable (fun u : ℝ ↦ |refinedSecondDensity u|) MeasureTheory.volume
      target028VariationLower target028VariationUpper := by
    apply hI.mono_set
    rw [Set.uIcc_of_le h0e, Set.uIcc_of_le hlu]
    exact Set.Icc_subset_Icc h0l hue
  have hIU :
    IntervalIntegrable (fun u : ℝ ↦ |refinedSecondDensity u|) MeasureTheory.volume
      target028VariationUpper (Real.exp (21 / 8 : ℝ)) := by
    apply hI.mono_set
    rw [Set.uIcc_of_le h0e, Set.uIcc_of_le hue]
    exact Set.Icc_subset_Icc h0u le_rfl
  have hsplit1 := intervalIntegral.integral_add_adjacent_intervals hIL hIM
  have hsplit2 := intervalIntegral.integral_add_adjacent_intervals (hIL.trans hIM) hIU
  have hL :
    (∫ u : ℝ in (0 : ℝ)..target028VariationLower, |refinedSecondDensity u|) =
      ∫ u : ℝ in (0 : ℝ)..target028VariationLower, refinedSecondDensity u := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with u hu
    rw [Set.uIoc_of_le h0l] at hu
    exact abs_of_nonneg (target028_density_lower hu.1 hu.2)
  have hM :
    (∫ u : ℝ in target028VariationLower..target028VariationUpper, |refinedSecondDensity u|) =
      -(∫ u : ℝ in target028VariationLower..target028VariationUpper, refinedSecondDensity u) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr_ae
    filter_upwards with u hu
    rw [Set.uIoc_of_le hlu] at hu
    exact abs_of_nonpos (target028_density_middle hu.1.le hu.2)
  have hU :
    (∫ u : ℝ in target028VariationUpper..Real.exp (21 / 8 : ℝ), |refinedSecondDensity u|) =
      ∫ u : ℝ in target028VariationUpper..Real.exp (21 / 8 : ℝ), refinedSecondDensity u := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with u hu
    rw [Set.uIoc_of_le hue] at hu
    have hup : 0 < target028VariationUpper := Real.exp_pos _
    have hpos : 0 < u := hup.trans hu.1
    exact abs_of_nonneg (target028_density_upper hu.1.le ((Real.log_le_iff_le_exp hpos).mpr hu.2))
  rw [← hsplit2, ← hsplit1, hL, hM, hU]
  ring

/-- The signed second density has zero integral over the full support.
The three exact logarithmic moments cancel algebraically. -/
theorem target028_density_integral_zero :
    (∫ u : ℝ in Set.Ioc 0 (Real.exp (21 / 8 : ℝ)), refinedSecondDensity u) = 0 := by
  have h3 := refined_density_moment 3 0 (by norm_num only)
  have h4 := refined_density_moment 4 0 (by norm_num only)
  have h5 := refined_density_moment 5 0 (by norm_num only)
  simp only [Real.rpow_zero, one_mul] at h3 h4 h5
  have he :
    refinedSecondDensity =
      (fun u : ℝ ↦
        (29 / 50 : ℝ) ^ 2 *
              (Real.exp (-refinedCoord u) / (120 * u * Real.sqrt u) * refinedCoord u ^ 5) -
            (10 * (29 / 50 : ℝ) * (27 / 25 : ℝ)) *
              (Real.exp (-refinedCoord u) / (120 * u * Real.sqrt u) * refinedCoord u ^ 4) +
          (20 * (27 / 25 : ℝ) ^ 2) *
            (Real.exp (-refinedCoord u) / (120 * u * Real.sqrt u) * refinedCoord u ^ 3)) := by
    funext u
    dsimp only [refinedSecondDensity]
    ring
  rw [he]
  have hi5 := h5.1.const_mul ((29 / 50 : ℝ) ^ 2)
  have hi4 := h4.1.const_mul (10 * (29 / 50 : ℝ) * (27 / 25 : ℝ))
  have hi3 := h3.1.const_mul (20 * (27 / 25 : ℝ) ^ 2)
  have hsum := MeasureTheory.integral_add (hi5.sub hi4) hi3
  have hsum2 := MeasureTheory.integral_sub hi5 hi4
  simp only [Pi.sub_apply] at hsum hsum2
  rw [hsum, hsum2, MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul, h5.2, h4.2, h3.2]
  norm_num only [Nat.factorial, Nat.reduceAdd, Nat.cast_ofNat]
  ring

/-- The absolute second variation equals minus twice the signed integral on
the middle interval. The full signed integral is zero, so the two outer pieces
cancel the middle piece exactly. -/
theorem target028_variation_eq_middle :
    (∫ u : ℝ in (0 : ℝ)..Real.exp (21 / 8 : ℝ), |refinedSecondDensity u|) =
      -2 * ∫ u : ℝ in target028VariationLower..target028VariationUpper, refinedSecondDensity u := by
  have hord := target028_variation_points_ordered
  have h0l : (0 : ℝ) ≤ target028VariationLower := hord.1.le
  have hlu := hord.2.1
  have hue := hord.2.2
  have h0u := h0l.trans hlu
  have h0e := h0u.trans hue
  have hI :
    IntervalIntegrable refinedSecondDensity MeasureTheory.volume 0 (Real.exp (21 / 8 : ℝ)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le h0e).mpr refined_second_integrable
  have hIL :
    IntervalIntegrable refinedSecondDensity MeasureTheory.volume 0 target028VariationLower := by
    apply hI.mono_set
    rw [Set.uIcc_of_le h0e, Set.uIcc_of_le h0l]
    exact Set.Icc_subset_Icc_right (hlu.trans hue)
  have hIM :
    IntervalIntegrable refinedSecondDensity MeasureTheory.volume target028VariationLower
      target028VariationUpper := by
    apply hI.mono_set
    rw [Set.uIcc_of_le h0e, Set.uIcc_of_le hlu]
    exact Set.Icc_subset_Icc h0l hue
  have hIU :
    IntervalIntegrable refinedSecondDensity MeasureTheory.volume target028VariationUpper
      (Real.exp (21 / 8 : ℝ)) := by
    apply hI.mono_set
    rw [Set.uIcc_of_le h0e, Set.uIcc_of_le hue]
    exact Set.Icc_subset_Icc h0u le_rfl
  have hsplit1 := intervalIntegral.integral_add_adjacent_intervals hIL hIM
  have hsplit2 := intervalIntegral.integral_add_adjacent_intervals (hIL.trans hIM) hIU
  have hzero : (∫ u : ℝ in (0 : ℝ)..Real.exp (21 / 8 : ℝ), refinedSecondDensity u) = 0 := by
    rw [intervalIntegral.integral_of_le h0e]
    exact target028_density_integral_zero
  have habs := target028_variation_signed_split
  rw [← hsplit2, ← hsplit1] at hzero
  linarith only [habs, hzero]

/-- The absolute second variation equals the difference of the logarithmic
weight slopes at the two sign-change points. The fundamental theorem evaluates
the middle signed integral without a polynomial majorant. -/
theorem target028_variation_eq_slopes :
    (∫ u : ℝ in (0 : ℝ)..Real.exp (21 / 8 : ℝ), |refinedSecondDensity u|) =
      2 *
        (target028VariationLower * refinedWeightDeriv target028VariationLower -
          target028VariationUpper * refinedWeightDeriv target028VariationUpper) := by
  have hord := target028_variation_points_ordered
  have h0l : (0 : ℝ) ≤ target028VariationLower := hord.1.le
  have hlu := hord.2.1
  have hue := hord.2.2
  have h0e := h0l.trans (hlu.trans hue)
  have hI :
    IntervalIntegrable refinedSecondDensity MeasureTheory.volume 0 (Real.exp (21 / 8 : ℝ)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le h0e).mpr refined_second_integrable
  have hIM :
    IntervalIntegrable refinedSecondDensity MeasureTheory.volume target028VariationLower
      target028VariationUpper := by
    apply hI.mono_set
    rw [Set.uIcc_of_le h0e, Set.uIcc_of_le hlu]
    exact Set.Icc_subset_Icc h0l hue
  have hmiddle :
    (∫ u : ℝ in target028VariationLower..target028VariationUpper, refinedSecondDensity u) =
      target028VariationUpper * refinedWeightDeriv target028VariationUpper -
        target028VariationLower * refinedWeightDeriv target028VariationLower := by
    apply
      intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t ↦ t * refinedWeightDeriv t) _ hIM
    intro u hu
    rw [Set.uIcc_of_le hlu] at hu
    exact refinedWeight_log_deriv (hord.1.trans_le hu.1)
  rw [target028_variation_eq_middle, hmiddle]
  ring

/-- Every weight with an integrable absolute variation admits the
same three-piece sign split. This applies to the square-root weight in the
principal error and keeps the cancellation needed for its sharp constant. -/
theorem target028_variation_weighted_split (w : ℝ → ℝ)
    (hI :
      IntervalIntegrable (fun u ↦ w u * |refinedSecondDensity u|) MeasureTheory.volume 0
        (Real.exp (21 / 8 : ℝ))) :
    (∫ u : ℝ in (0 : ℝ)..Real.exp (21 / 8 : ℝ), w u * |refinedSecondDensity u|) =
      (∫ u : ℝ in (0 : ℝ)..target028VariationLower, w u * refinedSecondDensity u) -
          (∫ u : ℝ in target028VariationLower..target028VariationUpper,
            w u * refinedSecondDensity u) +
        ∫ u : ℝ in target028VariationUpper..Real.exp (21 / 8 : ℝ),
          w u * refinedSecondDensity u := by
  have hord := target028_variation_points_ordered
  have h0l : (0 : ℝ) ≤ target028VariationLower := hord.1.le
  have hlu := hord.2.1
  have hue := hord.2.2
  have h0u := h0l.trans hlu
  have h0e := h0u.trans hue
  have hIL :
    IntervalIntegrable (fun u ↦ w u * |refinedSecondDensity u|) MeasureTheory.volume 0
      target028VariationLower := by
    apply hI.mono_set
    rw [Set.uIcc_of_le h0e, Set.uIcc_of_le h0l]
    exact Set.Icc_subset_Icc_right (hlu.trans hue)
  have hIM :
    IntervalIntegrable (fun u ↦ w u * |refinedSecondDensity u|) MeasureTheory.volume
      target028VariationLower target028VariationUpper := by
    apply hI.mono_set
    rw [Set.uIcc_of_le h0e, Set.uIcc_of_le hlu]
    exact Set.Icc_subset_Icc h0l hue
  have hIU :
    IntervalIntegrable (fun u ↦ w u * |refinedSecondDensity u|) MeasureTheory.volume
      target028VariationUpper (Real.exp (21 / 8 : ℝ)) := by
    apply hI.mono_set
    rw [Set.uIcc_of_le h0e, Set.uIcc_of_le hue]
    exact Set.Icc_subset_Icc h0u le_rfl
  have hsplit1 := intervalIntegral.integral_add_adjacent_intervals hIL hIM
  have hsplit2 := intervalIntegral.integral_add_adjacent_intervals (hIL.trans hIM) hIU
  have hL :
    (∫ u : ℝ in (0 : ℝ)..target028VariationLower, w u * |refinedSecondDensity u|) =
      ∫ u : ℝ in (0 : ℝ)..target028VariationLower, w u * refinedSecondDensity u := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with u hu
    rw [Set.uIoc_of_le h0l] at hu
    rw [abs_of_nonneg (target028_density_lower hu.1 hu.2)]
  have hM :
    (∫ u : ℝ in target028VariationLower..target028VariationUpper, w u * |refinedSecondDensity u|) =
      -(∫ u : ℝ in target028VariationLower..target028VariationUpper,
          w u * refinedSecondDensity u) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr_ae
    filter_upwards with u hu
    rw [Set.uIoc_of_le hlu] at hu
    rw [abs_of_nonpos (target028_density_middle hu.1.le hu.2), mul_neg]
  have hU :
    (∫ u : ℝ in target028VariationUpper..Real.exp (21 / 8 : ℝ), w u * |refinedSecondDensity u|) =
      ∫ u : ℝ in target028VariationUpper..Real.exp (21 / 8 : ℝ), w u * refinedSecondDensity u := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with u hu
    rw [Set.uIoc_of_le hue] at hu
    have hup : 0 < target028VariationUpper := Real.exp_pos _
    have hpos : 0 < u := hup.trans hu.1
    rw [abs_of_nonneg (target028_density_upper hu.1.le ((Real.log_le_iff_le_exp hpos).mpr hu.2))]
  rw [← hsplit2, ← hsplit1, hL, hM, hU]
  ring

/-- The square-root-weighted absolute variation splits into its three exact
signed pieces. Integrability follows from the existing variation bound. -/
theorem target028_sqrt_variation_signed_split :
    (∫ u : ℝ in (0 : ℝ)..Real.exp (21 / 8 : ℝ), Real.sqrt u * |refinedSecondDensity u|) =
      (∫ u : ℝ in (0 : ℝ)..target028VariationLower, Real.sqrt u * refinedSecondDensity u) -
          (∫ u : ℝ in target028VariationLower..target028VariationUpper,
            Real.sqrt u * refinedSecondDensity u) +
        ∫ u : ℝ in target028VariationUpper..Real.exp (21 / 8 : ℝ),
          Real.sqrt u * refinedSecondDensity u := by
  apply target028_variation_weighted_split Real.sqrt
  exact
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (Real.exp_pos _).le).mpr
      refined_second_variation.1

/-- The signed square-root-weighted second density has integral `25/108` on
the full support. Evaluate its three logarithmic moments exactly; the common
exponential factors cancel. -/
theorem target028_sqrt_density_integral :
    (∫ u : ℝ in Set.Ioc 0 (Real.exp (21 / 8 : ℝ)), Real.sqrt u * refinedSecondDensity u) =
      25 / 108 := by
  have h3 := refined_density_moment 3 (1 / 2) (by norm_num only)
  have h4 := refined_density_moment 4 (1 / 2) (by norm_num only)
  have h5 := refined_density_moment 5 (1 / 2) (by norm_num only)
  simp only [← Real.sqrt_eq_rpow] at h3 h4 h5
  have he :
    (fun u : ℝ ↦ Real.sqrt u * refinedSecondDensity u) =
      (fun u : ℝ ↦
        (29 / 50 : ℝ) ^ 2 *
              (Real.sqrt u * Real.exp (-refinedCoord u) / (120 * u * Real.sqrt u) *
                refinedCoord u ^ 5) -
            (10 * (29 / 50 : ℝ) * (27 / 25 : ℝ)) *
              (Real.sqrt u * Real.exp (-refinedCoord u) / (120 * u * Real.sqrt u) *
                refinedCoord u ^ 4) +
          (20 * (27 / 25 : ℝ) ^ 2) *
            (Real.sqrt u * Real.exp (-refinedCoord u) / (120 * u * Real.sqrt u) *
              refinedCoord u ^ 3)) := by
    funext u
    dsimp only [refinedSecondDensity]
    ring
  rw [he]
  have hi5 := h5.1.const_mul ((29 / 50 : ℝ) ^ 2)
  have hi4 := h4.1.const_mul (10 * (29 / 50 : ℝ) * (27 / 25 : ℝ))
  have hi3 := h3.1.const_mul (20 * (27 / 25 : ℝ) ^ 2)
  have hsum := MeasureTheory.integral_add (hi5.sub hi4) hi3
  have hsum2 := MeasureTheory.integral_sub hi5 hi4
  simp only [Pi.sub_apply] at hsum hsum2
  rw [hsum, hsum2, MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul, h5.2, h4.2, h3.2]
  norm_num only [Nat.factorial, Nat.reduceAdd, Nat.cast_ofNat]
  have hexp : Real.exp (-(567 / 200 : ℝ)) * Real.exp (567 / 200 : ℝ) = 1 := by
    rw [← Real.exp_add]
    norm_num only [neg_add_cancel, Real.exp_zero]
  nlinarith only [hexp]

/-- The square-root-weighted absolute variation is `25/108` minus twice the
middle signed integral. The full signed moment and three-piece split retain
the cancellation needed for the sharp principal-error constant. -/
theorem target028_sqrt_variation_eq_middle :
    (∫ u : ℝ in (0 : ℝ)..Real.exp (21 / 8 : ℝ), Real.sqrt u * |refinedSecondDensity u|) =
      (25 / 108 : ℝ) -
        2 *
          ∫ u : ℝ in target028VariationLower..target028VariationUpper,
            Real.sqrt u * refinedSecondDensity u := by
  have hord := target028_variation_points_ordered
  have h0l : (0 : ℝ) ≤ target028VariationLower := hord.1.le
  have hlu := hord.2.1
  have hue := hord.2.2
  have h0u := h0l.trans hlu
  have h0e := h0u.trans hue
  have hi :=
    MeasureTheory.IntegrableOn.mul_continuousOn_of_subset refined_second_integrable
      Real.continuous_sqrt.continuousOn measurableSet_Ioc isCompact_Icc
      (Set.Ioc_subset_Icc_self : Set.Ioc (0 : ℝ) (Real.exp (21 / 8 : ℝ)) ⊆ _)
  have hi' :
    MeasureTheory.IntegrableOn (fun u : ℝ ↦ Real.sqrt u * refinedSecondDensity u)
      (Set.Ioc 0 (Real.exp (21 / 8 : ℝ))) := by
    simpa only [mul_comm] using hi
  have hI :
    IntervalIntegrable (fun u : ℝ ↦ Real.sqrt u * refinedSecondDensity u) MeasureTheory.volume 0
      (Real.exp (21 / 8 : ℝ)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le h0e).mpr hi'
  have hIL :
    IntervalIntegrable (fun u : ℝ ↦ Real.sqrt u * refinedSecondDensity u) MeasureTheory.volume 0
      target028VariationLower := by
    apply hI.mono_set
    rw [Set.uIcc_of_le h0e, Set.uIcc_of_le h0l]
    exact Set.Icc_subset_Icc_right (hlu.trans hue)
  have hIM :
    IntervalIntegrable (fun u : ℝ ↦ Real.sqrt u * refinedSecondDensity u) MeasureTheory.volume
      target028VariationLower target028VariationUpper := by
    apply hI.mono_set
    rw [Set.uIcc_of_le h0e, Set.uIcc_of_le hlu]
    exact Set.Icc_subset_Icc h0l hue
  have hIU :
    IntervalIntegrable (fun u : ℝ ↦ Real.sqrt u * refinedSecondDensity u) MeasureTheory.volume
      target028VariationUpper (Real.exp (21 / 8 : ℝ)) := by
    apply hI.mono_set
    rw [Set.uIcc_of_le h0e, Set.uIcc_of_le hue]
    exact Set.Icc_subset_Icc h0u le_rfl
  have hsplit1 := intervalIntegral.integral_add_adjacent_intervals hIL hIM
  have hsplit2 := intervalIntegral.integral_add_adjacent_intervals (hIL.trans hIM) hIU
  have htotal :
    (∫ u : ℝ in (0 : ℝ)..Real.exp (21 / 8 : ℝ), Real.sqrt u * refinedSecondDensity u) =
      25 / 108 := by
    rw [intervalIntegral.integral_of_le h0e]
    exact target028_sqrt_density_integral
  have habs := target028_sqrt_variation_signed_split
  rw [← hsplit2, ← hsplit1] at htotal
  linarith only [habs, htotal]

/-- An explicit primitive for the square-root-weighted second density.
The polynomial is chosen so differentiation cancels its lower powers. -/
noncomputable def target028SqrtPrimitive (u : ℝ) : ℝ :=
  let v := refinedCoord u
  Real.exp (-v) *
    ((841 * v ^ 5 - 11455 * v ^ 4 + 12500 * v ^ 3 + 37500 * v ^ 2 + 75000 * v + 75000) / 324000)

/-- At a positive argument the explicit primitive differentiates to the
square-root-weighted second density. The square-root factors cancel and the
remaining polynomial identity is exact. -/
theorem target028_sqrt_primitive_deriv {u : ℝ} (hu : 0 < u) :
    HasDerivAt target028SqrtPrimitive (Real.sqrt u * refinedSecondDensity u) u := by
  have hv := refinedCoord_hasDerivAt hu
  have hp0 :=
    ((((((hv.pow 5).const_mul 841).sub ((hv.pow 4).const_mul 11455)).add
                  ((hv.pow 3).const_mul 12500)).add
              ((hv.pow 2).const_mul 37500)).add
          (hv.const_mul 75000)).add
      (hasDerivAt_const u 75000)
  have hp := hp0.div_const 324000
  have hd := hv.neg.exp.mul hp
  apply hd.congr_deriv
  dsimp only [target028SqrtPrimitive, refinedSecondDensity, Pi.mul_apply, Pi.sub_apply,
    Pi.add_apply, Pi.div_apply, Pi.pow_apply, Pi.neg_apply]
  norm_num only [Nat.reduceSub, Nat.cast_ofNat, pow_one]
  have hs0 : Real.sqrt u ≠ 0 := (Real.sqrt_pos.mpr hu).ne'
  field_simp (disch :=
    first
    | exact hu.ne'
    | exact hs0
    | norm_num only)
  ring

/-- The square-root-weighted absolute variation is an explicit difference of
the primitive at the two sign-change points, plus the exact signed total.
This reduces the sharp numeric bound to endpoint estimates. -/
theorem target028_sqrt_variation_eq_primitive :
    (∫ u : ℝ in (0 : ℝ)..Real.exp (21 / 8 : ℝ), Real.sqrt u * |refinedSecondDensity u|) =
      (25 / 108 : ℝ) +
        2 *
          (target028SqrtPrimitive target028VariationLower -
            target028SqrtPrimitive target028VariationUpper) := by
  have hord := target028_variation_points_ordered
  have h0l : (0 : ℝ) ≤ target028VariationLower := hord.1.le
  have hlu := hord.2.1
  have hue := hord.2.2
  have h0e := h0l.trans (hlu.trans hue)
  have hi :=
    MeasureTheory.IntegrableOn.mul_continuousOn_of_subset refined_second_integrable
      Real.continuous_sqrt.continuousOn measurableSet_Ioc isCompact_Icc
      (Set.Ioc_subset_Icc_self : Set.Ioc (0 : ℝ) (Real.exp (21 / 8 : ℝ)) ⊆ _)
  have hi' :
    MeasureTheory.IntegrableOn (fun u : ℝ ↦ Real.sqrt u * refinedSecondDensity u)
      (Set.Ioc 0 (Real.exp (21 / 8 : ℝ))) := by
    simpa only [mul_comm] using hi
  have hI :
    IntervalIntegrable (fun u : ℝ ↦ Real.sqrt u * refinedSecondDensity u) MeasureTheory.volume 0
      (Real.exp (21 / 8 : ℝ)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le h0e).mpr hi'
  have hIM :
    IntervalIntegrable (fun u : ℝ ↦ Real.sqrt u * refinedSecondDensity u) MeasureTheory.volume
      target028VariationLower target028VariationUpper := by
    apply hI.mono_set
    rw [Set.uIcc_of_le h0e, Set.uIcc_of_le hlu]
    exact Set.Icc_subset_Icc h0l hue
  have hmiddle :
    (∫ u : ℝ in target028VariationLower..target028VariationUpper,
        Real.sqrt u * refinedSecondDensity u) =
      target028SqrtPrimitive target028VariationUpper -
        target028SqrtPrimitive target028VariationLower := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := target028SqrtPrimitive) _ hIM
    intro u hu
    rw [Set.uIcc_of_le hlu] at hu
    exact target028_sqrt_primitive_deriv (hord.1.trans_le hu.1)
  rw [target028_sqrt_variation_eq_middle, hmiddle]
  ring

/-- The exponential support point with scaled logarithmic coordinate `x`.
Both sign-change points are obtained by substituting `5 ± sqrt 5`. -/
noncomputable def target028VariationPoint (x : ℝ) : ℝ :=
  Real.exp (21 / 8 - (50 / 29) * x)

/-- The refined coordinate at a variation point is a fixed rational multiple
of its scalar coordinate. This removes logarithms from endpoint evaluation. -/
theorem target028_coord_at_point (x : ℝ) :
    refinedCoord (target028VariationPoint x) = (54 / 29 : ℝ) * x := by
  dsimp only [refinedCoord, target028VariationPoint]
  rw [Real.log_exp]
  ring

/-- At a variation point, the logarithmic weight slope is a polynomial in the
scalar coordinate times a single negative exponential. This exact expression
reduces the unweighted variation constant to rational endpoint bounds. -/
theorem target028_slope_at_point (x : ℝ) :
    target028VariationPoint x * refinedWeightDeriv (target028VariationPoint x) =
      ((27 / 25 : ℝ) * (54 / 29 : ℝ) ^ 4 / 120) * x ^ 4 * (x - 5) *
        Real.exp (-(21 / 16 : ℝ) - x) := by
  have hp : target028VariationPoint x ≠ 0 := (Real.exp_pos _).ne'
  have hs :
    Real.sqrt (target028VariationPoint x) = Real.exp ((21 / 8 - (50 / 29 : ℝ) * x) / 2) := by
    dsimp only [target028VariationPoint]
    exact (Real.exp_half _).symm
  have he :
    Real.exp (-((54 / 29 : ℝ) * x)) / Real.exp ((21 / 8 - (50 / 29 : ℝ) * x) / 2) =
      Real.exp (-(21 / 16 : ℝ) - x) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  dsimp only [refinedWeightDeriv]
  rw [target028_coord_at_point, hs]
  calc
    _ =
        ((27 / 25 : ℝ) * (54 / 29 : ℝ) ^ 4 / 120) * x ^ 4 * (x - 5) *
          (Real.exp (-((54 / 29 : ℝ) * x)) / Real.exp ((21 / 8 - (50 / 29 : ℝ) * x) / 2)) :=
      by
      field_simp (disch :=
        first
        | exact hp
        | exact (Real.exp_ne_zero _)
        | norm_num only)
      ring
    _ = _ := by rw [he]

/-- The unweighted absolute variation is an explicit two-term exponential
expression at `5 ± sqrt 5`. The signs of the two endpoint slopes are retained
exactly, so the remaining task is a finite rational enclosure. -/
theorem target028_variation_explicit :
    (∫ u : ℝ in (0 : ℝ)..Real.exp (21 / 8 : ℝ), |refinedSecondDensity u|) =
      2 * ((27 / 25 : ℝ) * (54 / 29 : ℝ) ^ 4 / 120) * Real.sqrt 5 *
        ((5 + Real.sqrt 5) ^ 4 * Real.exp (-(21 / 16 : ℝ) - (5 + Real.sqrt 5)) +
          (5 - Real.sqrt 5) ^ 4 * Real.exp (-(21 / 16 : ℝ) - (5 - Real.sqrt 5))) := by
  rw [target028_variation_eq_slopes]
  change
    2 *
        (target028VariationPoint (5 + Real.sqrt 5) *
            refinedWeightDeriv (target028VariationPoint (5 + Real.sqrt 5)) -
          target028VariationPoint (5 - Real.sqrt 5) *
            refinedWeightDeriv (target028VariationPoint (5 - Real.sqrt 5))) =
      _
  rw [target028_slope_at_point, target028_slope_at_point]
  ring

end PseudoPrime.PrimeTestBounds.MillerRabin
