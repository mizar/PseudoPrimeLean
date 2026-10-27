/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ExponentialRampCutoff
public import PseudoPrime.Analysis.QuadraticGammaSmoothedNumerics

/-! # Absolute variation bounds for the exponential ramp -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The smooth variation density (u-1)exp(-u) before the ramp.
Its signed integral has an explicit primitive; its absolute integral controls
the lower-sum error in the double-partial-summation functional. -/
noncomputable def exponentialRampVariationLeft (u : ℝ) : ℝ :=
  (u - 1) * Real.exp (-u)

/-- The smooth variation density inside the ramp, with width 1/200.
It is nonnegative on [247/100,99/40]. Its integral and the two jump masses
control the lower-sum error without discarding the derivative discontinuities. -/
noncomputable def exponentialRampVariationMiddle (u : ℝ) : ℝ :=
  Real.exp (-u) * ((u - 1) * ((99 / 40 - u) / (1 / 200)) + (2 * u - 1) / (1 / 200))

/-- The first density is continuous by the polynomial-exponential product rule.
This supplies finite-interval integrability, including its absolute value. -/
private theorem left_continuous : Continuous exponentialRampVariationLeft :=
  (continuous_id.sub continuous_const).mul (Real.continuous_exp.comp continuous_id.neg)

/-- On any real interval [a,b], the first density integrates to
-b exp(-b)+a exp(-a). Differentiate its primitive and apply the fundamental
theorem of calculus. This evaluates the two pieces of its absolute integral. -/
theorem left_density_integral (a b : ℝ) :
    (∫ u in a..b, exponentialRampVariationLeft u) = -b * Real.exp (-b) + a * Real.exp (-a) := by
  have hd (u : ℝ) :
    HasDerivAt (fun v : ℝ ↦ -v * Real.exp (-v)) (exponentialRampVariationLeft u) u := by
    have h := (hasDerivAt_id u).neg.mul (exponentialRamp_first_derivative u)
    apply h.congr_deriv
    change (-1) * Real.exp (-u) + (-u) * (-Real.exp (-u)) = (u - 1) * Real.exp (-u)
    ring
  have h :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ ↦ hd u)
      (left_continuous.intervalIntegrable a b)
  exact h.trans (by ring)

/-- The first absolute density integral through 247/100 is at most one.
Split at its sign change u=1 and retain the negative endpoint correction.
The resulting 2 exp(-1) is at most one because exp(1)>=2.
This sharper bound avoids fractional Gamma moments in the ramp error estimate. -/
theorem left_abs_integral_le_one :
    (∫ u in (0 : ℝ)..(247 / 100), |exponentialRampVariationLeft u|) ≤ 1 := by
  have hl :
    (∫ u in (0 : ℝ)..1, |exponentialRampVariationLeft u|) =
      -(∫ u in (0 : ℝ)..1, exponentialRampVariationLeft u) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro u hu
    rw [Set.uIcc_of_le (by norm_num only : (0 : ℝ) ≤ 1)] at hu
    dsimp only
    exact abs_of_nonpos (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hu.2) (Real.exp_pos _).le)
  have hr :
    (∫ u in (1 : ℝ)..(247 / 100), |exponentialRampVariationLeft u|) =
      ∫ u in (1 : ℝ)..(247 / 100), exponentialRampVariationLeft u := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [Set.uIcc_of_le (by norm_num only : (1 : ℝ) ≤ 247 / 100)] at hu
    dsimp only
    exact abs_of_nonneg (mul_nonneg (sub_nonneg.mpr hu.1) (Real.exp_pos _).le)
  rw [←
    intervalIntegral.integral_add_adjacent_intervals
      (left_continuous.abs.intervalIntegrable (0 : ℝ) 1)
      (left_continuous.abs.intervalIntegrable (1 : ℝ) (247 / 100)),
    hl, hr, left_density_integral, left_density_integral]
  have h := Real.add_one_le_exp (1 : ℝ)
  have hinv : Real.exp (-1 : ℝ) ≤ 1 / 2 := by
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (by norm_num only : (0 : ℝ) < 2) (by linarith only [h])
  nlinarith only [hinv, (Real.exp_pos (-(247 / 100 : ℝ))).le]

/-- Eleven positive Taylor terms certify exp(-247/100)<=423/5000.
Take reciprocals of the positive lower bound. This bounds the middle density
and the magnitude of the left derivative jump. -/
theorem ramp_exp_left_le : Real.exp (-(247 / 100 : ℝ)) ≤ (423 / 5000 : ℝ) := by
  have ht : (5000 / 423 : ℝ) ≤ ∑ k ∈ Finset.range 11, (247 / 100 : ℝ) ^ k / (k.factorial : ℝ) := by
    norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  have he := ht.trans (Real.sum_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 247 / 100) 11)
  have hi := one_div_le_one_div_of_le (by norm_num only : (0 : ℝ) < 5000 / 423) he
  rw [Real.exp_neg, ← one_div]
  norm_num only at hi
  exact hi

/-- The middle density is continuous as a polynomial-exponential expression.
This supplies the integrability required for integral monotonicity. -/
private theorem middle_continuous : Continuous exponentialRampVariationMiddle :=
  (Real.continuous_exp.comp continuous_id.neg).mul
    (((continuous_id.sub continuous_const).mul
          ((continuous_const.sub continuous_id).div_const (1 / 200))).add
      ((continuous_const.mul continuous_id).sub continuous_const |>.div_const (1 / 200)))

/-- On the ramp interval, its middle variation density is nonnegative and
at most the displayed constant using exp(-247/100). Bound the ramp factor by
one and the remaining linear factors at the right endpoint.
This controls the entire interval rather than a finite set of sample points. -/
theorem middle_density_bounds {u : ℝ} (hu : (247 / 100 : ℝ) ≤ u) (hub : u ≤ 99 / 40) :
    0 ≤ exponentialRampVariationMiddle u ∧
      exponentialRampVariationMiddle u ≤
        Real.exp (-(247 / 100 : ℝ)) * ((99 / 40 - 1) + (2 * (99 / 40) - 1) / (1 / 200)) := by
  have hr0 : 0 ≤ (99 / 40 - u) / (1 / 200 : ℝ) := div_nonneg (sub_nonneg.mpr hub) (by norm_num only)
  have hr1 : (99 / 40 - u) / (1 / 200 : ℝ) ≤ 1 := by
    norm_num only [div_le_iff₀]
    linarith only [hu]
  have hu1 : 0 ≤ u - 1 := by linarith only [hu]
  have hu2 : 0 ≤ 2 * u - 1 := by linarith only [hu]
  have hp0 :=
    add_nonneg (mul_nonneg hu1 hr0) (div_nonneg hu2 (by norm_num only : (0 : ℝ) ≤ 1 / 200))
  have hp1 := mul_le_mul (sub_le_sub_right hub 1) hr1 hr0 (by norm_num only : (0 : ℝ) ≤ 99 / 40 - 1)
  have hp2 : (2 * u - 1) / (1 / 200 : ℝ) ≤ (2 * (99 / 40) - 1) / (1 / 200) := by linarith only [hub]
  have he := Real.exp_le_exp.mpr (neg_le_neg hu)
  refine ⟨mul_nonneg (Real.exp_pos _).le hp0, ?_⟩
  exact mul_le_mul he (by linarith only [hp1, hp2]) hp0 (Real.exp_pos _).le

/-- The middle absolute density integral is at most the displayed left-endpoint
exponential times its rational interval allowance. Integrate the pointwise constant
bound over the width 1/200. This supplies the smooth middle part of the variation mass. -/
theorem middle_abs_integral_le :
    (∫ u in (247 / 100 : ℝ)..(99 / 40), |exponentialRampVariationMiddle u|) ≤
      Real.exp (-(247 / 100 : ℝ)) * ((99 / 40 - 1) * (1 / 200) + (2 * (99 / 40) - 1)) := by
  have hi :=
    intervalIntegral.integral_mono_on (μ := MeasureTheory.volume)
      (by norm_num only : (247 / 100 : ℝ) ≤ 99 / 40)
      (middle_continuous.abs.intervalIntegrable (247 / 100 : ℝ) (99 / 40))
      (continuous_const.intervalIntegrable (247 / 100 : ℝ) (99 / 40)) (g := fun _ ↦
      Real.exp (-(247 / 100 : ℝ)) * ((99 / 40 - 1) + (2 * (99 / 40) - 1) / (1 / 200)))
      (fun u hu ↦ by
        rw [abs_of_nonneg (middle_density_bounds hu.1 hu.2).1]
        exact (middle_density_bounds hu.1 hu.2).2)
  rw [intervalIntegral.integral_const, smul_eq_mul] at hi
  nlinarith only [hi]

/-- The total absolute variation mass of the ramp: the two absolute density
integrals and both positive magnitudes of the signed derivative jumps.
This quantity controls the norm of the complete error functional. -/
noncomputable def exponentialRampVariationMass : ℝ :=
  (∫ u in (0 : ℝ)..(247 / 100), |exponentialRampVariationLeft u|) +
    (∫ u in (247 / 100 : ℝ)..(99 / 40), |exponentialRampVariationMiddle u|) +
    (247 / 100) * Real.exp (-(247 / 100 : ℝ)) / (1 / 200) +
    (99 / 40) * Real.exp (-(99 / 40 : ℝ)) / (1 / 200)

/-- The actual total absolute variation mass, including both jumps, is at most 85.
Use the first-density bound one, the middle interval bound and the two rational
exponential certificates. This improves the proposal's allowance 86. -/
theorem variation_mass_le_85 : exponentialRampVariationMass ≤ 85 := by
  have ha :=
    mul_le_mul_of_nonneg_left ramp_exp_left_le
      (by norm_num only :
        (0 : ℝ) ≤ ((99 / 40 - 1) * (1 / 200) + (2 * (99 / 40) - 1)) + (247 / 100) / (1 / 200))
  have hb :=
    mul_le_mul_of_nonneg_left gamma_ramp_exp_cutoff_le
      (by norm_num only : (0 : ℝ) ≤ (99 / 40) / (1 / 200))
  change
    (∫ u in (0 : ℝ)..(247 / 100), |exponentialRampVariationLeft u|) +
        (∫ u in (247 / 100 : ℝ)..(99 / 40), |exponentialRampVariationMiddle u|) +
        (247 / 100) * Real.exp (-(247 / 100 : ℝ)) / (1 / 200) +
        (99 / 40) * Real.exp (-(99 / 40 : ℝ)) / (1 / 200) ≤
      85
  linarith only [left_abs_integral_le_one, middle_abs_integral_le, ha, hb]

/-- For u<=99/40, sqrt(u)<=63/40. Apply the square-root comparison and
check the rational square. This bounds the square-root error uniformly on the ramp support. -/
theorem sqrt_le_ramp_right {u : ℝ} (hu : u ≤ 99 / 40) : Real.sqrt u ≤ 63 / 40 := by
  apply Real.sqrt_le_iff.mpr
  exact ⟨by norm_num only, hu.trans (by norm_num only)⟩

end PseudoPrime.Analysis
