/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleDoubleAbel

/-! # Second variation for the refined principal weight -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A nonnegative polynomial majorant for the refined second Abel density on the
positive support. Its logarithmic moments provide explicit principal-sum errors. -/
noncomputable def refinedSecondMajorant (u : ℝ) : ℝ :=
  Real.exp (-refinedCoord u) / (120 * u * Real.sqrt u) *
    ((29 / 50 : ℝ) ^ 2 * refinedCoord u ^ 5 +
      10 * (29 / 50 : ℝ) * (27 / 25 : ℝ) * refinedCoord u ^ 4 +
      20 * (27 / 25 : ℝ) ^ 2 * refinedCoord u ^ 3)

/-- The absolute second density is bounded by its polynomial majorant on the support.
Use positivity of the logarithmic coordinate and the triangle inequality. -/
theorem refined_second_abs_le {u : ℝ} (hu : 0 < u) (hl : Real.log u ≤ 21 / 8) :
    |refinedSecondDensity u| ≤ refinedSecondMajorant u := by
  have hv : 0 ≤ refinedCoord u := by
    dsimp only [refinedCoord]
    linarith only [hl]
  have hbase : 0 ≤ Real.exp (-refinedCoord u) / (120 * u * Real.sqrt u) :=
    div_nonneg (Real.exp_nonneg _)
      (mul_nonneg (mul_nonneg (by norm_num only) hu.le) (Real.sqrt_nonneg _))
  have ha : 0 ≤ (29 / 50 : ℝ) ^ 2 * refinedCoord u ^ 5 := mul_nonneg (sq_nonneg _) (pow_nonneg hv _)
  have hb : 0 ≤ 10 * (29 / 50 : ℝ) * (27 / 25 : ℝ) * refinedCoord u ^ 4 :=
    mul_nonneg (by norm_num only) (pow_nonneg hv _)
  have hc : 0 ≤ 20 * (27 / 25 : ℝ) ^ 2 * refinedCoord u ^ 3 :=
    mul_nonneg (by norm_num only) (pow_nonneg hv _)
  have htriangle :=
    abs_add_le
      ((29 / 50 : ℝ) ^ 2 * refinedCoord u ^ 5 -
        10 * (29 / 50 : ℝ) * (27 / 25 : ℝ) * refinedCoord u ^ 4)
      (20 * (27 / 25 : ℝ) ^ 2 * refinedCoord u ^ 3)
  have hsub :=
    abs_sub ((29 / 50 : ℝ) ^ 2 * refinedCoord u ^ 5)
      (10 * (29 / 50 : ℝ) * (27 / 25 : ℝ) * refinedCoord u ^ 4)
  rw [abs_of_nonneg ha, abs_of_nonneg hb] at hsub
  rw [abs_of_nonneg hc] at htriangle
  dsimp only [refinedSecondDensity, refinedSecondMajorant]
  rw [abs_mul, abs_of_nonneg hbase]
  exact mul_le_mul_of_nonneg_left (by linarith only [htriangle, hsub]) hbase

/-- The square-root-weighted second-density majorant is integrable with exact
integral `6889/2700`. Evaluate its three logarithmic moments and cancel exponentials. -/
theorem refined_second_majorant_integral :
    MeasureTheory.IntegrableOn (fun u : ℝ ↦ Real.sqrt u * refinedSecondMajorant u)
        (Set.Ioc 0 (Real.exp (21 / 8 : ℝ))) ∧
      (∫ u : ℝ in Set.Ioc 0 (Real.exp (21 / 8 : ℝ)), Real.sqrt u * refinedSecondMajorant u) =
        (6889 / 2700 : ℝ) := by
  have h3 := refined_density_moment 3 (1 / 2) (by norm_num only)
  have h4 := refined_density_moment 4 (1 / 2) (by norm_num only)
  have h5 := refined_density_moment 5 (1 / 2) (by norm_num only)
  simp only [← Real.sqrt_eq_rpow] at h3 h4 h5
  have he :
    (fun u : ℝ ↦ Real.sqrt u * refinedSecondMajorant u) =
      (fun u : ℝ ↦
        (29 / 50 : ℝ) ^ 2 *
            (Real.sqrt u * Real.exp (-refinedCoord u) / (120 * u * Real.sqrt u) *
              refinedCoord u ^ 5) +
          (10 * (29 / 50 : ℝ) * (27 / 25 : ℝ)) *
            (Real.sqrt u * Real.exp (-refinedCoord u) / (120 * u * Real.sqrt u) *
              refinedCoord u ^ 4) +
          (20 * (27 / 25 : ℝ) ^ 2) *
            (Real.sqrt u * Real.exp (-refinedCoord u) / (120 * u * Real.sqrt u) *
              refinedCoord u ^ 3)) := by
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
  have hexp : Real.exp (-(567 / 200 : ℝ)) * Real.exp (567 / 200 : ℝ) = 1 := by
    rw [← Real.exp_add]
    norm_num only [neg_add_cancel, Real.exp_zero]
  nlinarith only [hexp]

/-- The square-root-weighted absolute second density is integrable and its integral
is at most `6889/2700`. Integrate the pointwise majorant on the entire support. -/
theorem refined_second_variation :
    MeasureTheory.IntegrableOn (fun u : ℝ ↦ Real.sqrt u * |refinedSecondDensity u|)
        (Set.Ioc 0 (Real.exp (21 / 8 : ℝ))) ∧
      (∫ u : ℝ in Set.Ioc 0 (Real.exp (21 / 8 : ℝ)), Real.sqrt u * |refinedSecondDensity u|) ≤
        (6889 / 2700 : ℝ) := by
  have hi :=
    MeasureTheory.IntegrableOn.mul_continuousOn_of_subset refined_second_integrable.norm
      Real.continuous_sqrt.continuousOn measurableSet_Ioc isCompact_Icc
      (Set.Ioc_subset_Icc_self : Set.Ioc (0 : ℝ) (Real.exp (21 / 8 : ℝ)) ⊆ _)
  simp only [Real.norm_eq_abs] at hi
  have hiL :
    MeasureTheory.IntegrableOn (fun u : ℝ ↦ Real.sqrt u * |refinedSecondDensity u|)
      (Set.Ioc 0 (Real.exp (21 / 8 : ℝ))) := by
    simpa only [mul_comm] using hi
  refine ⟨hiL, ?_⟩
  rw [← refined_second_majorant_integral.2]
  apply MeasureTheory.integral_mono_ae hiL refined_second_majorant_integral.1
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with u hu
  have hl : Real.log u ≤ 21 / 8 := (Real.log_le_iff_le_exp hu.1).mpr hu.2
  exact mul_le_mul_of_nonneg_left (refined_second_abs_le hu.1 hl) (Real.sqrt_nonneg _)

end PseudoPrime.PrimeTestBounds.MillerRabin
