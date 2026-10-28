/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GaussianMR240Numerics

/-! # Sharp quadratic coefficient comparison for the unchanged Gaussian MR bound -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For L>=240, the radius is below 18L/25. Bound the square root of this
linear cap by 11L/200 and compare the quadratic budget at that point.
The estimate supplies the coefficient comparison used for both Gamma prefixes. -/
theorem gaussianMR6_radius_upper240 {L : ℝ} (hL : 240 ≤ L) :
    gaussianMR6Radius L < (18 / 25 : ℝ) * L := by
  let u := Real.sqrt ((18 / 25 : ℝ) * L)
  let s := gaussianMR6Root L
  have hL0 : 0 ≤ L := by linarith only [hL]
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hu2 : u ^ 2 = (18 / 25 : ℝ) * L := Real.sq_sqrt (mul_nonneg (by norm_num only) hL0)
  have hu : u ≤ (11 / 200 : ℝ) * L := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · exact mul_nonneg (by norm_num only) hL0
    · have hm := mul_nonneg hL0 (sub_nonneg.mpr hL)
      nlinarith only [hm, hL]
  have hs : 13 ≤ s := by
    have h := gaussianMR6_root_lower hL
    linarith only [h]
  have he := gaussianMR6_equation hL0
  change
    gaussianMR6FifthsD * s ^ 2 =
      gaussianMR6FifthsConductor * L + gaussianMR6FifthsBeta * s + 6 at he
  have hd := gaussianMR6Fifths_coefficients_pos.1
  have hc :
    (1 / 40 : ℝ) <
      gaussianMR6FifthsD * (18 / 25) - gaussianMR6FifthsConductor -
        gaussianMR6FifthsBeta * (11 / 200) := by
    norm_num only [gaussianMR6FifthsD, gaussianMR6FifthsBeta, gaussianMR6FifthsConductor,
      gaussianMR6FifthsIndex, gaussianMR6FifthsMass, gaussianMR6FifthsEndpoint]
  have hscale := mul_lt_mul_of_pos_right hc (by linarith only [hL] : 0 < L)
  have hbeta := mul_le_mul_of_nonneg_left hu gaussianMR6Fifths_coefficients_pos.2.le
  have hdu := congrArg (fun x : ℝ ↦ gaussianMR6FifthsD * x) hu2
  have hv :
    0 <
      gaussianMR6FifthsD * u ^ 2 - gaussianMR6FifthsBeta * u - gaussianMR6FifthsConductor * L -
        6 := by
    nlinarith only [hdu, hscale, hbeta, hL]
  by_contra hn
  have hr := le_of_not_gt hn
  have hus : u ≤ s := by
    apply (sq_le_sq₀ hu0 (by linarith only [hs] : 0 ≤ s)).mp
    change u ^ 2 ≤ gaussianMR6Radius L
    rw [hu2]
    exact hr
  have hb : 0 < gaussianMR6FifthsD * 13 - gaussianMR6FifthsBeta := by
    norm_num only [gaussianMR6FifthsD, gaussianMR6FifthsBeta, gaussianMR6FifthsIndex,
      gaussianMR6FifthsMass, gaussianMR6FifthsEndpoint]
  have hmul := mul_le_mul_of_nonneg_left (by linarith only [hs, hu0] : (13 : ℝ) ≤ s + u) hd.le
  have hf : 0 ≤ gaussianMR6FifthsD * (s + u) - gaussianMR6FifthsBeta := by linarith only [hb, hmul]
  have hp := mul_nonneg (sub_nonneg.mpr hus) hf
  nlinarith only [he, hv, hp]

/-- For L>=240, the B6 witness bound is below 0.63L squared.
Square the positive radius cap and compare rational coefficients. This separates
B6 from the Gamma prefix bounds throughout their common applicable range. -/
theorem gaussianMR6Bound_lt_063_sq {L : ℝ} (hL : 240 ≤ L) :
    gaussianMR6Bound L < (63 / 100 : ℝ) * L ^ 2 := by
  have hr := gaussianMR6_radius_upper240 hL
  have hp : 0 ≤ gaussianMR6Radius L := sq_nonneg _
  have hs := (sq_lt_sq₀ hp (hp.trans hr.le)).mpr hr
  have hscaled := mul_lt_mul_of_pos_left hs (by norm_num only : (0 : ℝ) < 6 / 5)
  dsimp only [gaussianMR6Bound]
  nlinarith only [hscaled, sq_pos_of_pos (by linarith only [hL] : 0 < L)]

/-- At L>=300 the unchanged radius is below 6989L/10000. Evaluate its quadratic
budget at the square root of that linear cap, bounding the latter by 181L/3750.
The positive-root comparison proves the estimate on the entire half-line. -/
theorem gaussianMR6_radius_upper_sharp {L : ℝ} (hL : 300 ≤ L) :
    gaussianMR6Radius L < (6989 / 10000 : ℝ) * L := by
  let u := Real.sqrt ((6989 / 10000 : ℝ) * L)
  let s := gaussianMR6Root L
  have hL0 : 0 ≤ L := by linarith only [hL]
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hu2 : u ^ 2 = (6989 / 10000 : ℝ) * L := Real.sq_sqrt (mul_nonneg (by norm_num only) hL0)
  have hu : u ≤ (181 / 3750 : ℝ) * L := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · exact mul_nonneg (by norm_num only) hL0
    · have hm := mul_nonneg hL0 (sub_nonneg.mpr hL)
      nlinarith only [hm, hL]
  have hs : 14 ≤ s := gaussianMR6Root_lower_14 hL
  have he := gaussianMR6Radius_equation hL
  change
    gaussianMR6FifthsD * s ^ 2 =
      gaussianMR6FifthsConductor * L + gaussianMR6FifthsBeta * s + 6 at he
  have hd := gaussianMR6Fifths_coefficients_pos.1
  have hc :
    (1 / 50 : ℝ) <
      gaussianMR6FifthsD * (6989 / 10000) - gaussianMR6FifthsConductor -
        gaussianMR6FifthsBeta * (181 / 3750) := by
    norm_num only [gaussianMR6FifthsD, gaussianMR6FifthsBeta, gaussianMR6FifthsConductor,
      gaussianMR6FifthsIndex, gaussianMR6FifthsMass, gaussianMR6FifthsEndpoint]
  have hscale := mul_lt_mul_of_pos_right hc (by linarith only [hL] : 0 < L)
  have hbeta := mul_le_mul_of_nonneg_left hu gaussianMR6Fifths_coefficients_pos.2.le
  have hdu := congrArg (fun x : ℝ ↦ gaussianMR6FifthsD * x) hu2
  have hv :
    0 <
      gaussianMR6FifthsD * u ^ 2 - gaussianMR6FifthsBeta * u - gaussianMR6FifthsConductor * L -
        6 := by
    nlinarith only [hdu, hscale, hbeta, hL]
  by_contra hn
  have hr := le_of_not_gt hn
  have hus : u ≤ s := by
    apply (sq_le_sq₀ hu0 (by linarith only [hs] : 0 ≤ s)).mp
    change u ^ 2 ≤ gaussianMR6Radius L
    rw [hu2]
    exact hr
  have hb : 0 < gaussianMR6FifthsD * 14 - gaussianMR6FifthsBeta := by
    norm_num only [gaussianMR6FifthsD, gaussianMR6FifthsBeta, gaussianMR6FifthsIndex,
      gaussianMR6FifthsMass, gaussianMR6FifthsEndpoint]
  have hmul := mul_le_mul_of_nonneg_left (by linarith only [hs, hu0] : (14 : ℝ) ≤ s + u) hd.le
  have hf : 0 ≤ gaussianMR6FifthsD * (s + u) - gaussianMR6FifthsBeta := by linarith only [hb, hmul]
  have hp := mul_nonneg (sub_nonneg.mpr hus) hf
  nlinarith only [he, hv, hp]

/-- At L>=300 the unchanged constant-six bound is below 0.5862 times L squared.
Square the sharp positive radius cap and compare exact rational coefficients.
This improves the presentation of the old formula without changing its values. -/
theorem gaussianMR6Bound_lt_05862_sq {L : ℝ} (hL : 300 ≤ L) :
    gaussianMR6Bound L < (2931 / 5000 : ℝ) * L ^ 2 := by
  have hr := gaussianMR6_radius_upper_sharp hL
  have hp : 0 ≤ gaussianMR6Radius L := sq_nonneg _
  have hs := (sq_lt_sq₀ hp (hp.trans hr.le)).mpr hr
  have hscaled := mul_lt_mul_of_pos_left hs (by norm_num only : (0 : ℝ) < 6 / 5)
  dsimp only [gaussianMR6Bound]
  nlinarith only [hscaled, sq_pos_of_pos (by linarith only [hL] : 0 < L)]

end PseudoPrime.Analysis
