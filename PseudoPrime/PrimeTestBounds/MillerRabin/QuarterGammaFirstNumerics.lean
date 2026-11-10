/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterGammaConvolutionIntegral
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterGammaExpLower
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterGammaExpUpper

/-! # First Gamma-pole moment on intervals -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The fifth exponential moment retained for the first Gamma pole is
nondecreasing as the upper endpoint moves to the right. Both endpoints are
nonnegative, so the integrand is nonnegative on the larger interval. -/
theorem quarter_first_moment_mono {z Z : ℝ} (hz : 0 ≤ z) (hZ : z ≤ Z) :
    Analysis.logPowerTailPoly (29 / 50) 5 0 -
        Real.exp (-(29 / 50 : ℝ) * z) * Analysis.logPowerTailPoly (29 / 50) 5 z ≤
      Analysis.logPowerTailPoly (29 / 50) 5 0 -
        Real.exp (-(29 / 50 : ℝ) * Z) * Analysis.logPowerTailPoly (29 / 50) 5 Z := by
  have hi := Analysis.exponential_moment_integrable (r := (29 / 50 : ℝ)) (by norm_num only) 5
  have hiZ := hi.mono_set (Set.Ioc_subset_Ioi_self : Set.Ioc (0 : ℝ) Z ⊆ Set.Ioi 0)
  have hn :
    ∀ᵐ v ∂MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) Z),
      0 ≤ v ^ 5 * Real.exp (-(29 / 50 : ℝ) * v) := by
    apply MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc
    intro v hv
    exact mul_nonneg (pow_nonneg hv.1.le _) (Real.exp_pos _).le
  have hsub : Set.Ioc (0 : ℝ) z ⊆ Set.Ioc (0 : ℝ) Z := fun _ hv ↦ ⟨hv.1, hv.2.trans hZ⟩
  have hm := MeasureTheory.setIntegral_mono_set hiZ hn (Filter.Eventually.of_forall hsub)
  have hZ0 : 0 ≤ Z := hz.trans hZ
  rw [Analysis.exponential_moment_interval (by norm_num only) hz 5,
    Analysis.exponential_moment_interval (by norm_num only) hZ0 5] at hm
  exact hm

/-- On a nonnegative interval, bound the first-pole correction below by the
moment at the left endpoint and the decreasing exponential at the right
endpoint. These endpoint values can be certified independently. -/
theorem quarter_first_correction_interval {a z b : ℝ} (ha : 0 ≤ a) (haz : a ≤ z) (hzb : z ≤ b) :
    (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-(1 / 2 : ℝ) * b)) *
        (Analysis.logPowerTailPoly (29 / 50) 5 0 -
          Real.exp (-(29 / 50 : ℝ) * a) * Analysis.logPowerTailPoly (29 / 50) 5 a) ≤
      quarterGammaFirstCorrection z := by
  have hm := quarter_first_moment_mono ha haz
  have hM :
    0 ≤
      Analysis.logPowerTailPoly (29 / 50) 5 0 -
        Real.exp (-(29 / 50 : ℝ) * a) * Analysis.logPowerTailPoly (29 / 50) 5 a := by
    have hi : 0 ≤ ∫ v in Set.Ioc (0 : ℝ) a, v ^ 5 * Real.exp (-(29 / 50 : ℝ) * v) := by
      apply MeasureTheory.setIntegral_nonneg measurableSet_Ioc
      intro v hv
      exact mul_nonneg (pow_nonneg hv.1.le _) (Real.exp_pos _).le
    rw [Analysis.exponential_moment_interval (by norm_num only) ha 5] at hi
    exact hi
  have hexp : Real.exp (-(1 / 2 : ℝ) * b) ≤ Real.exp (-(1 / 2 : ℝ) * z) :=
    Real.exp_le_exp.mpr (by linarith only [hzb])
  have hprod := mul_le_mul hexp hm hM (Real.exp_pos _).le
  have hh := mul_le_mul_of_nonneg_left hprod (show 0 ≤ (27 / 25 : ℝ) ^ 5 / 120 by positivity)
  simpa only [quarterGammaFirstCorrection, mul_assoc] using hh

/-- For shifted scales from `13` through `53/4`, the first Gamma pole
contributes at least `19/500`. The two exponential endpoints are certified
independently, and the fifth-moment endpoint comparison covers the interval. -/
theorem quarter_first_correction_13_1325 {z : ℝ} (hz : 13 ≤ z) (hZ : z ≤ 53 / 4) :
    (19 / 500 : ℝ) ≤ quarterGammaFirstCorrection z := by
  have h := quarter_first_correction_interval (a := 13) (b := 53 / 4) (by norm_num only) hz hZ
  have hpoly : 0 ≤ Analysis.logPowerTailPoly (29 / 50 : ℝ) 5 13 := by
    norm_num only [Analysis.logPowerTailPoly]
  have hm := mul_le_mul_of_nonneg_right quarter_gamma_exp_upper hpoly
  have hM :
    Analysis.logPowerTailPoly (29 / 50 : ℝ) 5 0 -
        (54 / 100000 : ℝ) * Analysis.logPowerTailPoly (29 / 50) 5 13 ≤
      Analysis.logPowerTailPoly (29 / 50) 5 0 -
        Real.exp (-(377 / 50 : ℝ)) * Analysis.logPowerTailPoly (29 / 50) 5 13 := by
    linarith only [hm]
  have hM0 :
    0 ≤
      Analysis.logPowerTailPoly (29 / 50 : ℝ) 5 0 -
        (54 / 100000 : ℝ) * Analysis.logPowerTailPoly (29 / 50) 5 13 := by
    norm_num only [Analysis.logPowerTailPoly]
  have he := quarter_gamma_exp_lower
  have hp := mul_le_mul he hM hM0 (Real.exp_pos _).le
  have hs := mul_le_mul_of_nonneg_left hp (show 0 ≤ (27 / 25 : ℝ) ^ 5 / 120 by positivity)
  norm_num only [Analysis.logPowerTailPoly] at hs h ⊢
  linarith only [hs, h]

end PseudoPrime.PrimeTestBounds.MillerRabin
