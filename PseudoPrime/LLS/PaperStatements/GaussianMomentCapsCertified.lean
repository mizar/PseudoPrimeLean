/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.GaussianMomentGridCertificate

/-! # Certified full Gaussian moment caps -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Left of -4, the tilted Gaussian density is bounded by a shifted Gaussian
moment times `exp(-16)`. The cutoff factor is at most one. -/
theorem gaussian_tilted_left_pointwise {k l v : ℝ} (hl : 0 ≤ l) (hv : v ≤ -4) :
    Analysis.normalizedGaussianWeight v * Real.exp (-k * v) * Real.exp (-l * Real.exp (-v)) ≤
      Real.exp (-16) * (Analysis.normalizedGaussianWeight v * Real.exp ((-k - 4) * v)) := by
  have hcut : Real.exp (-l * Real.exp (-v)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hl) (Real.exp_pos _).le)
  have hbase := mul_pos (Analysis.normalizedGaussianWeight_pos v) (Real.exp_pos (-k * v))
  have h1 := mul_le_of_le_one_right hbase.le hcut
  have ha : -k * v ≤ -16 + (-k - 4) * v := by nlinarith only [hv]
  have h2 :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ha) (Analysis.normalizedGaussianWeight_pos v).le
  rw [Real.exp_add] at h2
  calc
    Analysis.normalizedGaussianWeight v * Real.exp (-k * v) * Real.exp (-l * Real.exp (-v)) ≤
        Analysis.normalizedGaussianWeight v * Real.exp (-k * v) :=
      h1
    _ ≤ Analysis.normalizedGaussianWeight v * (Real.exp (-16) * Real.exp ((-k - 4) * v)) := h2
    _ = Real.exp (-16) * (Analysis.normalizedGaussianWeight v * Real.exp ((-k - 4) * v)) := by ring

/-- Right of 4, the tilted Gaussian density is bounded by a shifted Gaussian
moment times `exp(-16)`. The cutoff factor is at most one. -/
theorem gaussian_tilted_right_pointwise {k l v : ℝ} (hl : 0 ≤ l) (hv : 4 ≤ v) :
    Analysis.normalizedGaussianWeight v * Real.exp (-k * v) * Real.exp (-l * Real.exp (-v)) ≤
      Real.exp (-16) * (Analysis.normalizedGaussianWeight v * Real.exp ((4 - k) * v)) := by
  have hcut : Real.exp (-l * Real.exp (-v)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hl) (Real.exp_pos _).le)
  have hbase := mul_pos (Analysis.normalizedGaussianWeight_pos v) (Real.exp_pos (-k * v))
  have h1 := mul_le_of_le_one_right hbase.le hcut
  have ha : -k * v ≤ -16 + (4 - k) * v := by nlinarith only [hv]
  have h2 :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ha) (Analysis.normalizedGaussianWeight_pos v).le
  rw [Real.exp_add] at h2
  calc
    Analysis.normalizedGaussianWeight v * Real.exp (-k * v) * Real.exp (-l * Real.exp (-v)) ≤
        Analysis.normalizedGaussianWeight v * Real.exp (-k * v) :=
      h1
    _ ≤ Analysis.normalizedGaussianWeight v * (Real.exp (-16) * Real.exp ((4 - k) * v)) := h2
    _ = Real.exp (-16) * (Analysis.normalizedGaussianWeight v * Real.exp ((4 - k) * v)) := by ring

/-- For nonnegative cutoff and an integrable tilted density, bound the full
integral by its integral over [-4,4] and two explicit Gaussian moments.
The two half-lines are dominated by shifted exponential moments. -/
theorem gaussian_tilted_full_integral_le {k l : ℝ} (hl : 0 ≤ l)
    (hf :
      MeasureTheory.Integrable
        (fun v : ℝ ↦
          Analysis.normalizedGaussianWeight v * Real.exp (-k * v) *
            Real.exp (-l * Real.exp (-v)))) :
    (∫ v : ℝ,
        Analysis.normalizedGaussianWeight v * Real.exp (-k * v) * Real.exp (-l * Real.exp (-v))) ≤
      (∫ v in (-4 : ℝ)..4,
          Analysis.normalizedGaussianWeight v * Real.exp (-k * v) * Real.exp (-l * Real.exp (-v))) +
        Real.exp (-16) * Real.exp ((-k - 4) ^ 2 / 4) +
        Real.exp (-16) * Real.exp ((4 - k) ^ 2 / 4) := by
  let f : ℝ → ℝ := fun v ↦
    Analysis.normalizedGaussianWeight v * Real.exp (-k * v) * Real.exp (-l * Real.exp (-v))
  let gL : ℝ → ℝ := fun v ↦
    Real.exp (-16) * (Analysis.normalizedGaussianWeight v * Real.exp ((-k - 4) * v))
  let gR : ℝ → ℝ := fun v ↦
    Real.exp (-16) * (Analysis.normalizedGaussianWeight v * Real.exp ((4 - k) * v))
  have hL : MeasureTheory.Integrable gL :=
    (Analysis.integrable_normalizedGaussian_mul_exp (-k - 4)).const_mul _
  have hR : MeasureTheory.Integrable gR :=
    (Analysis.integrable_normalizedGaussian_mul_exp (4 - k)).const_mul _
  have hl1 :=
    MeasureTheory.setIntegral_mono_on (s := Set.Iic (-4 : ℝ)) hf.integrableOn hL.integrableOn
      measurableSet_Iic (fun v hv ↦ gaussian_tilted_left_pointwise hl hv)
  have hr1 :=
    MeasureTheory.setIntegral_mono_on (s := Set.Ioi (4 : ℝ)) hf.integrableOn hR.integrableOn
      measurableSet_Ioi (fun v hv ↦ gaussian_tilted_right_pointwise hl hv.le)
  have hl2 :=
    MeasureTheory.setIntegral_le_integral (s := Set.Iic (-4 : ℝ)) hL
      (Filter.Eventually.of_forall
        (fun v ↦
          mul_nonneg (Real.exp_pos _).le
            (mul_nonneg (Analysis.normalizedGaussianWeight_pos v).le (Real.exp_pos _).le)))
  have hr2 :=
    MeasureTheory.setIntegral_le_integral (s := Set.Ioi (4 : ℝ)) hR
      (Filter.Eventually.of_forall
        (fun v ↦
          mul_nonneg (Real.exp_pos _).le
            (mul_nonneg (Analysis.normalizedGaussianWeight_pos v).le (Real.exp_pos _).le)))
  have hl3 := hl1.trans hl2
  have hr3 := hr1.trans hr2
  change (∫ v in Set.Iic (-4 : ℝ), f v) ≤ ∫ v : ℝ, gL v at hl3
  change (∫ v in Set.Ioi (4 : ℝ), f v) ≤ ∫ v : ℝ, gR v at hr3
  dsimp only [gL] at hl3
  dsimp only [gR] at hr3
  rw [MeasureTheory.integral_const_mul, Analysis.integral_normalizedGaussian_mul_exp] at hl3 hr3
  have hsplit :=
    intervalIntegral.integral_Iic_add_Ioi (b := (-4 : ℝ)) hf.integrableOn hf.integrableOn
  have hsplit2 :=
    intervalIntegral.integral_interval_add_Ioi (a := (-4 : ℝ)) (b := (4 : ℝ)) hf.integrableOn
      hf.integrableOn
  change (∫ v in Set.Iic (-4 : ℝ), f v) + (∫ v in Set.Ioi (-4 : ℝ), f v) = ∫ v : ℝ, f v at hsplit
  change
    (∫ v in (-4 : ℝ)..4, f v) + (∫ v in Set.Ioi (4 : ℝ), f v) =
      ∫ v in Set.Ioi (-4 : ℝ), f v at hsplit2
  change (∫ v : ℝ, f v) ≤ (∫ v in (-4 : ℝ)..4, f v) + _ + _
  linarith only [hl3, hr3, hsplit, hsplit2]

/-- The exponential tail factor at -8 is at most 1/2800.
A finite positive Taylor sum bounds `exp(8)` from below. -/
theorem exp_neg_eight_le_one_div_2800 : Real.exp (-8) ≤ (1 / 2800 : ℝ) := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 8) 14
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial_succ,
    Nat.factorial_zero, Nat.cast_ofNat] at h
  rw [Real.exp_neg, ← one_div, div_le_iff₀ (Real.exp_pos 8)]
  nlinarith only [h]

/-- Twice `exp(-15/16)` is at most 79/100.
Invert a positive Taylor lower bound for `exp(15/16)`. -/
theorem exp_neg_fifteen_sixteenth_le : 2 * Real.exp (-(15 / 16 : ℝ)) ≤ 79 / 100 := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 15 / 16) 7
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial_succ,
    Nat.factorial_zero, Nat.cast_ofNat] at h
  rw [Real.exp_neg, ← one_div]
  have hp := Real.exp_pos (15 / 16 : ℝ)
  rw [show 2 * (1 / Real.exp (15 / 16 : ℝ)) = 2 / Real.exp (15 / 16 : ℝ) by ring]
  apply (div_le_iff₀ hp).2
  nlinarith only [h]

/-- The full profile moment exceeds its [-4,4] integral by at most 1/1400.
Both tails are bounded by the explicit exponential moment at -8. -/
theorem gaussian_profile_tail_bound :
    (∫ v : ℝ, Analysis.gaussianGammaProfileIntegrand (21 / 10) v) ≤
      (∫ v in (-4 : ℝ)..4, Analysis.gaussianGammaProfileIntegrand (21 / 10) v) + 1 / 1400 := by
  have hf :=
    Analysis.integrable_gaussianGammaProfileIntegrand (by norm_num only : (0 : ℝ) ≤ 21 / 10)
  have hfi :
    MeasureTheory.Integrable
      (fun v : ℝ ↦
        Analysis.normalizedGaussianWeight v * Real.exp (-(1 / 2 : ℝ) * v) *
          Real.exp (-(21 / 10 : ℝ) * Real.exp (-v))) := by
    convert hf using 1
    funext v
    rfl
  have h := gaussian_tilted_full_integral_le (k := 1 / 2) (l := 21 / 10) (by norm_num only) hfi
  rw [← Real.exp_add, ← Real.exp_add] at h
  norm_num only at h
  have hL : Real.exp (-(175 / 16 : ℝ)) ≤ Real.exp (-8) := Real.exp_le_exp.mpr (by norm_num only)
  have hR : Real.exp (-(207 / 16 : ℝ)) ≤ Real.exp (-8) := Real.exp_le_exp.mpr (by norm_num only)
  have htail := exp_neg_eight_le_one_div_2800
  change
    (∫ v : ℝ,
        Analysis.normalizedGaussianWeight v * Real.exp (-(1 / 2 : ℝ) * v) *
          Real.exp (-(21 / 10 : ℝ) * Real.exp (-v))) ≤
      (∫ v in (-4 : ℝ)..4,
          Analysis.normalizedGaussianWeight v * Real.exp (-(1 / 2 : ℝ) * v) *
            Real.exp (-(21 / 10 : ℝ) * Real.exp (-v))) +
        1 / 1400
  linarith only [h, hL, hR, htail]

/-- The full endpoint moment exceeds its [-4,4] integral by at most 1/1400.
Both tails are bounded by the explicit exponential moment at -8. -/
theorem gaussian_endpoint_tail_bound :
    (∫ v : ℝ, gaussianEndpointDensity (21 / 10) v) ≤
      (∫ v in (-4 : ℝ)..4, gaussianEndpointDensity (21 / 10) v) + 1 / 1400 := by
  have hf := integrable_gaussianEndpointDensity (by norm_num only : (0 : ℝ) ≤ 21 / 10)
  have hfi :
    MeasureTheory.Integrable
      (fun v : ℝ ↦
        Analysis.normalizedGaussianWeight v * Real.exp (-(3 / 2 : ℝ) * v) *
          Real.exp (-(21 / 10 : ℝ) * Real.exp (-v))) := by
    convert hf using 1
    funext v
    rfl
  have h := gaussian_tilted_full_integral_le (k := 3 / 2) (l := 21 / 10) (by norm_num only) hfi
  rw [← Real.exp_add, ← Real.exp_add] at h
  norm_num only at h
  have hL : Real.exp (-(135 / 16 : ℝ)) ≤ Real.exp (-8) := Real.exp_le_exp.mpr (by norm_num only)
  have hR : Real.exp (-(231 / 16 : ℝ)) ≤ Real.exp (-8) := Real.exp_le_exp.mpr (by norm_num only)
  have htail := exp_neg_eight_le_one_div_2800
  change
    (∫ v : ℝ,
        Analysis.normalizedGaussianWeight v * Real.exp (-(3 / 2 : ℝ) * v) *
          Real.exp (-(21 / 10 : ℝ) * Real.exp (-v))) ≤
      (∫ v in (-4 : ℝ)..4,
          Analysis.normalizedGaussianWeight v * Real.exp (-(3 / 2 : ℝ) * v) *
            Real.exp (-(21 / 10 : ℝ) * Real.exp (-v))) +
        1 / 1400
  linarith only [h, hL, hR, htail]

/-- The two full Gaussian moment caps required for the sharp principal bound
hold at cutoff ratio 21/10. Combine the kernel-certified finite grid, explicit
tail moments, and the rational exponential estimate. -/
theorem gaussian_moment_caps_21_10 :
    (∫ v : ℝ, Analysis.gaussianGammaProfileIntegrand (21 / 10) v) ≤ 7 / 50 ∧
      (21 / 10 : ℝ) * (∫ v : ℝ, gaussianEndpointDensity (21 / 10) v) +
          2 * Real.exp (-1) * Real.exp (1 / 16 : ℝ) ≤
        1 := by
  have hfinite := gaussian_grid_finite_moment_bounds
  have hp := gaussian_profile_tail_bound
  have he := gaussian_endpoint_tail_bound
  have hexp := exp_neg_fifteen_sixteenth_le
  have hcomb : 2 * Real.exp (-1) * Real.exp (1 / 16 : ℝ) = 2 * Real.exp (-(15 / 16 : ℝ)) := by
    rw [mul_assoc, ← Real.exp_add]
    norm_num only
  rw [hcomb]
  constructor
  · linarith only [hfinite.1, hp]
  · linarith only [hfinite.2, he, hexp]

end PseudoPrime.LLS.PaperStatements
