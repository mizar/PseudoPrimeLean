/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterGammaConvolutionIntegral
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterGammaTailAlgebra

/-! Splitting the positive-pole Gamma convolution at its shifted scale. -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For nonnegative shift and pole parameter, split the Gamma convolution at the shift.
Absolute-value simplification gives the left and right exponential integrals. -/
theorem quarter_gamma_convolution_split {z c : ℝ} (hz : 0 ≤ z) (hc : 0 ≤ c) :
    quarterGammaConvolution z c =
      (∫ v in Set.Ioc (0 : ℝ) z, quarterGammaDensity v * Real.exp (-c * (z - v))) +
        ∫ v in Set.Ioi z, quarterGammaDensity v * Real.exp (-c * (v - z)) := by
  have hi := quarter_gamma_convolution_integrable z hc
  have hi1 := hi.mono_set (Set.Ioc_subset_Ioi_self : Set.Ioc (0 : ℝ) z ⊆ Set.Ioi 0)
  have hi2 := hi.mono_set (Set.Ioi_subset_Ioi hz)
  have he1 :
    (∫ v in Set.Ioc (0 : ℝ) z, quarterGammaDensity v * Real.exp (-c * |v - z|)) =
      ∫ v in Set.Ioc (0 : ℝ) z, quarterGammaDensity v * Real.exp (-c * (z - v)) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
    intro v hv
    dsimp only
    rw [abs_of_nonpos (sub_nonpos.mpr hv.2), neg_sub]
  have he2 :
    (∫ v in Set.Ioi z, quarterGammaDensity v * Real.exp (-c * |v - z|)) =
      ∫ v in Set.Ioi z, quarterGammaDensity v * Real.exp (-c * (v - z)) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro v hv
    dsimp only
    rw [abs_of_nonneg (sub_nonneg.mpr hv.le)]
  unfold quarterGammaConvolution
  rw [← Set.Ioc_union_Ioi_eq_Ioi hz,
    MeasureTheory.setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi hi1 hi2, he1, he2]

/-- For nonnegative shift and pole rate, the upper half of the convolution is the
closed fifth exponential tail. This supplies the right contribution in the pole estimate. -/
theorem quarter_gamma_right_moment {z c : ℝ} (hz : 0 ≤ z) (hc : 0 ≤ c) :
    (∫ v in Set.Ioi z, quarterGammaDensity v * Real.exp (-c * (v - z))) =
      (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-(27 / 25 : ℝ) * z)) *
        Analysis.logPowerTailPoly (c + 27 / 25) 5 z := by
  have hr : 0 < c + (27 / 25 : ℝ) := by linarith only [hc]
  have he :
    (∫ v in Set.Ioi z, quarterGammaDensity v * Real.exp (-c * (v - z))) =
      ∫ v in Set.Ioi z,
        (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (c * z)) *
          (v ^ 5 * Real.exp (-(c + 27 / 25) * v)) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro v hv
    dsimp only
    rw [quarterGammaDensity, ite_eq_left (hz.trans hv.le)]
    rw [mul_assoc _ (Real.exp _) (Real.exp _), ← Real.exp_add]
    have hexp : -(27 / 25 : ℝ) * v + -c * (v - z) = c * z + -(c + 27 / 25) * v := by ring
    rw [hexp, Real.exp_add]
    ring
  rw [he, MeasureTheory.integral_const_mul, Analysis.exponential_moment_tail hr hz 5]
  rw [mul_assoc ((27 / 25 : ℝ) ^ 5 / 120), ← mul_assoc (Real.exp _) (Real.exp _), ← Real.exp_add]
  have hexp : c * z + -(c + 27 / 25) * z = -(27 / 25 : ℝ) * z := by ring
  rw [hexp, mul_assoc]

/-- For a nonnegative shift and pole rate, express the Gamma convolution as an initial
moment plus its closed upper tail. This prepares the higher-pole comparison. -/
theorem quarter_gamma_convolution_moments {z c : ℝ} (hz : 0 ≤ z) (hc : 0 ≤ c) :
    quarterGammaConvolution z c =
      (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-c * z)) *
          (∫ v in Set.Ioc (0 : ℝ) z, v ^ 5 * Real.exp (-((27 / 25 : ℝ) - c) * v)) +
        (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-(27 / 25 : ℝ) * z)) *
          Analysis.logPowerTailPoly (c + 27 / 25) 5 z := by
  rw [quarter_gamma_convolution_split hz hc, quarter_gamma_initial_moment,
    quarter_gamma_right_moment hz hc]

/-- For a nonnegative shift and nonnegative pole rate different from the profile rate,
evaluate both halves of the Gamma convolution in closed form. -/
theorem quarter_gamma_convolution_closed {z c : ℝ} (hz : 0 ≤ z) (hc : 0 ≤ c)
    (hne : c ≠ (27 / 25 : ℝ)) :
    quarterGammaConvolution z c =
      (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-c * z)) *
          (Analysis.logPowerTailPoly (27 / 25 - c) 5 0 -
            Real.exp (-((27 / 25 : ℝ) - c) * z) * Analysis.logPowerTailPoly (27 / 25 - c) 5 z) +
        (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-(27 / 25 : ℝ) * z)) *
          Analysis.logPowerTailPoly (c + 27 / 25) 5 z := by
  have hr : (27 / 25 : ℝ) - c ≠ 0 := sub_ne_zero.mpr hne.symm
  rw [quarter_gamma_convolution_moments hz hc, Analysis.exponential_moment_interval_ne hr hz 5]

/-- For every later Gamma pole, separate the closed convolution into its polynomial
part and the positive exponential endpoint term. -/
theorem quarter_gamma_convolution_expansion {z c : ℝ} (hz : 0 ≤ z) (hc : 0 ≤ c)
    (hne : c ≠ (27 / 25 : ℝ)) :
    quarterGammaConvolution z c =
      (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-(27 / 25 : ℝ) * z)) *
          (Analysis.logPowerTailPoly (c + 27 / 25) 5 z -
            Analysis.logPowerTailPoly (27 / 25 - c) 5 z) +
        (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-c * z)) *
          Analysis.logPowerTailPoly (27 / 25 - c) 5 0 := by
  rw [quarter_gamma_convolution_closed hz hc hne]
  have hexp :
    Real.exp (-c * z) * Real.exp (-((27 / 25 : ℝ) - c) * z) = Real.exp (-(27 / 25 : ℝ) * z) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [← hexp]
  ring

/-- At every nonzero rate, the fifth tail polynomial at zero is the positive
sixth reciprocal moment. This proves the endpoint term has the required sign. -/
theorem quarter_gamma_tail_poly_zero {r : ℝ} (hr : r ≠ 0) :
    Analysis.logPowerTailPoly r 5 0 = 120 / r ^ 6 := by
  norm_num only [Analysis.logPowerTailPoly, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_div, zero_add, Nat.cast_ofNat]
  field_simp [hr]
  norm_num only

/-- For the later poles and scales at least twelve, the two polynomial moments
dominate the baseline after normalization by the fifth power of the scale. -/
theorem quarter_gamma_poly_bound {z c : ℝ} (hz : 12 ≤ z) (hc : (5 / 2 : ℝ) ≤ c) :
    2 / c ≤
      (Analysis.logPowerTailPoly (c + 27 / 25) 5 z - Analysis.logPowerTailPoly (27 / 25 - c) 5 z) /
        z ^ 5 := by
  have hz0 : 0 < z := by linarith only [hz]
  have hc0 : 0 < c := by linarith only [hc]
  have hm : 0 < c - (27 / 25 : ℝ) := by linarith only [hc]
  have hp : 0 < c + (27 / 25 : ℝ) := by linarith only [hc]
  have hm' : c * 25 - 27 ≠ 0 := by linarith only [hm]
  have hm'' : 27 - c * 25 ≠ 0 := by linarith only [hm]
  let Q : ℝ :=
    20 / z ^ 2 / (c + 27 / 25) ^ 3 + 60 / z ^ 3 / (c + 27 / 25) ^ 4 +
      120 / z ^ 4 / (c + 27 / 25) ^ 5 +
      120 / z ^ 5 / (c + 27 / 25) ^ 6
  have hQ : 0 ≤ Q := by
    dsimp only [Q]
    positivity
  apply quarter_gamma_tail_of_expansion hz hc hQ
  have heq :
    2 / c +
        2 * (27 / 25 : ℝ) * (z * (27 / 25 : ℝ) * (c ^ 2 - (27 / 25 : ℝ) ^ 2) - 10 * c ^ 2) /
          (z * c * (c - 27 / 25) ^ 2 * (c + 27 / 25) ^ 2) +
        (20 / z ^ 2 / (c - 27 / 25) ^ 3 - 60 / z ^ 3 / (c - 27 / 25) ^ 4 +
          (120 / z ^ 4 / (c - 27 / 25) ^ 5 - 120 / z ^ 5 / (c - 27 / 25) ^ 6)) +
        Q =
      (Analysis.logPowerTailPoly (c + 27 / 25) 5 z - Analysis.logPowerTailPoly (27 / 25 - c) 5 z) /
        z ^ 5 := by
    dsimp only [Q, Analysis.logPowerTailPoly]
    field_simp [hz0.ne', hc0.ne', hm.ne', hp.ne', hm', hm'']
    ring
  exact le_of_eq heq

/-- At scales at least twelve and rates of later Gamma poles, the convolution
dominates twice the local density divided by the pole rate. -/
theorem quarter_gamma_convolution_ge_density {z c : ℝ} (hz : 12 ≤ z) (hc : (5 / 2 : ℝ) ≤ c) :
    (2 / c) * quarterGammaDensity z ≤ quarterGammaConvolution z c := by
  have hz0 : 0 < z := by linarith only [hz]
  have hc0 : 0 ≤ c := by linarith only [hc]
  have hne : c ≠ (27 / 25 : ℝ) := by linarith only [hc]
  have hr : (27 / 25 : ℝ) - c ≠ 0 := sub_ne_zero.mpr hne.symm
  have hpoly := (le_div_iff₀ (pow_pos hz0 5)).mp (quarter_gamma_poly_bound hz hc)
  have hcoef : 0 ≤ ((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-(27 / 25 : ℝ) * z) := by positivity
  have hend :
    0 ≤
      (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-c * z)) *
        Analysis.logPowerTailPoly (27 / 25 - c) 5 0 := by
    rw [quarter_gamma_tail_poly_zero hr]
    positivity
  have hh := mul_le_mul_of_nonneg_left hpoly hcoef
  rw [quarter_gamma_convolution_expansion hz0.le hc0 hne, quarterGammaDensity, ite_eq_left hz0.le]
  nlinarith only [hh, hend]

/-- For every later Gamma pole at a shifted scale at least twelve, the normalized
resolvent integral dominates the local profile. This is the sign of each paired term. -/
theorem quarter_gamma_pole_ge_density {y c : ℝ} (hy : 12 ≤ y + 21 / 8) (hc : (5 / 2 : ℝ) ≤ c) :
    quarterGammaDensity (y + 21 / 8) ≤
      (1 / (2 * Real.pi)) * c ^ 2 *
        (∫ t : ℝ,
            (refinedSixPoleKernel.function (Complex.I * t) *
                Complex.exp (Complex.I * (t : ℂ) * y)) *
              ((1 / (c ^ 2 + t ^ 2) : ℝ) : ℂ)).re := by
  have hc0 : 0 < c := by linarith only [hc]
  rw [quarter_pole_convolution_real y hc0]
  have h :=
    mul_le_mul_of_nonneg_left (quarter_gamma_convolution_ge_density hy hc)
      (show 0 ≤ c / 2 by positivity)
  have he : c / 2 * (2 / c) = 1 := by field_simp
  rw [← mul_assoc, he, one_mul] at h
  exact h

end PseudoPrime.PrimeTestBounds.MillerRabin
