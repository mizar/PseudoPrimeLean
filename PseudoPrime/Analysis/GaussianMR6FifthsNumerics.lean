/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GaussianMRVariableRelativeNumerics

/-! # Numerical inputs for the 6/5 Gaussian MR bound -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The mass retained by the 6/5 Gaussian cutoff certificate. -/
noncomputable def gaussianMR6FifthsMass : ℝ :=
  16 / 25

/-- The endpoint exponential cap shared with the existing Gaussian branches. -/
noncomputable def gaussianMR6FifthsEndpoint : ℝ :=
  2129 / 2000

/-- The index threshold for the large-index 6/5 branch. -/
noncomputable def gaussianMR6FifthsIndex : ℝ :=
  1000000000

/-- The conductor coefficient in the 6/5 budget. -/
noncomputable def gaussianMR6FifthsConductor : ℝ :=
  161 / 400

/-- The quadratic coefficient after eliminating the subgroup index. -/
noncomputable def gaussianMR6FifthsD : ℝ :=
  (gaussianMR6FifthsIndex * gaussianMR6FifthsMass - gaussianMR6FifthsEndpoint) /
    (gaussianMR6FifthsIndex - 1)

/-- The square-root coefficient after eliminating the subgroup index. -/
noncomputable def gaussianMR6FifthsBeta : ℝ :=
  (gaussianMR6FifthsIndex / (gaussianMR6FifthsIndex - 1)) * (gaussianMR6FifthsMass / 3 + 3 / 10)

/-- Positive root of the planned 6/5 Gaussian budget equation. -/
noncomputable def gaussianMR6FifthsRoot (L : ℝ) : ℝ :=
  (gaussianMR6FifthsBeta +
      Real.sqrt
        (gaussianMR6FifthsBeta ^ 2 +
          4 * gaussianMR6FifthsD * (gaussianMR6FifthsConductor * L + 29))) /
    (2 * gaussianMR6FifthsD)

/-- Radius defined by the positive root of the 6/5 Gaussian budget. -/
noncomputable def gaussianMR6FifthsRadius (L : ℝ) : ℝ :=
  gaussianMR6FifthsRoot L ^ 2

/-- The proposed 6/5 Gaussian witness upper bound. -/
noncomputable def gaussianMR6FifthsBound (L : ℝ) : ℝ :=
  (6 / 5 : ℝ) * gaussianMR6FifthsRadius L ^ 2

/-- Positive root of the 6/5 Gaussian budget with analysis13's additive
constant 18. -/
noncomputable def gaussianMR18Root (L : ℝ) : ℝ :=
  (gaussianMR6FifthsBeta +
      Real.sqrt
        (gaussianMR6FifthsBeta ^ 2 +
          4 * gaussianMR6FifthsD * (gaussianMR6FifthsConductor * L + 18))) /
    (2 * gaussianMR6FifthsD)

/-- Radius determined by the constant-18 Gaussian budget. -/
noncomputable def gaussianMR18Radius (L : ℝ) : ℝ :=
  gaussianMR18Root L ^ 2

/-- Candidate 6/5 witness bound from analysis13. -/
noncomputable def gaussianMR18Bound (L : ℝ) : ℝ :=
  (6 / 5 : ℝ) * gaussianMR18Radius L ^ 2

/-- Positive root of the Gaussian MR budget with additive constant 6. -/
noncomputable def gaussianMR6Root (L : ℝ) : ℝ :=
  (gaussianMR6FifthsBeta +
      Real.sqrt
        (gaussianMR6FifthsBeta ^ 2 +
          4 * gaussianMR6FifthsD * (gaussianMR6FifthsConductor * L + 6))) /
    (2 * gaussianMR6FifthsD)

/-- Squared radius associated with the constant-6 Gaussian MR budget. -/
noncomputable def gaussianMR6Radius (L : ℝ) : ℝ :=
  gaussianMR6Root L ^ 2

/-- The proposed B6 witness bound with additive constant 6. -/
noncomputable def gaussianMR6Bound (L : ℝ) : ℝ :=
  (6 / 5 : ℝ) * gaussianMR6Radius L ^ 2

/-- The constant-18 root is positive from logarithmic scale 300 onward. -/
theorem gaussianMR18Root_pos {L : ℝ} (hL : 300 ≤ L) : 0 < gaussianMR18Root L := by
  have hD : 0 < gaussianMR6FifthsD := by
    norm_num only [gaussianMR6FifthsD, gaussianMR6FifthsIndex, gaussianMR6FifthsMass,
      gaussianMR6FifthsEndpoint]
  have hB : 0 < gaussianMR6FifthsBeta := by
    norm_num only [gaussianMR6FifthsBeta, gaussianMR6FifthsIndex, gaussianMR6FifthsMass]
  have hC : 0 < gaussianMR6FifthsConductor := by norm_num only [gaussianMR6FifthsConductor]
  have harg :
    0 <
      gaussianMR6FifthsBeta ^ 2 +
        4 * gaussianMR6FifthsD * (gaussianMR6FifthsConductor * L + 18) := by
    have hL' : 0 ≤ L := by linarith only [hL]
    have ht : 0 < gaussianMR6FifthsConductor * L + 18 := by nlinarith only [hC, hL']
    positivity
  have hnum :
    0 <
      gaussianMR6FifthsBeta +
        Real.sqrt
          (gaussianMR6FifthsBeta ^ 2 +
            4 * gaussianMR6FifthsD * (gaussianMR6FifthsConductor * L + 18)) :=
    add_pos_of_pos_of_nonneg hB (Real.sqrt_nonneg _)
  have hden : 0 < 2 * gaussianMR6FifthsD := by positivity
  dsimp only [gaussianMR18Root]
  exact div_pos hnum hden

/-- The constant-18 radius satisfies its defining quadratic budget. -/
theorem gaussianMR18Radius_equation {L : ℝ} (hL : 300 ≤ L) :
    gaussianMR6FifthsD * gaussianMR18Radius L =
      gaussianMR6FifthsConductor * L + gaussianMR6FifthsBeta * gaussianMR18Root L + 18 := by
  let z :=
    Real.sqrt
      (gaussianMR6FifthsBeta ^ 2 + 4 * gaussianMR6FifthsD * (gaussianMR6FifthsConductor * L + 18))
  have hD : 0 < gaussianMR6FifthsD := by
    norm_num only [gaussianMR6FifthsD, gaussianMR6FifthsIndex, gaussianMR6FifthsMass,
      gaussianMR6FifthsEndpoint]
  have hB : 0 < gaussianMR6FifthsBeta := by
    norm_num only [gaussianMR6FifthsBeta, gaussianMR6FifthsIndex, gaussianMR6FifthsMass]
  have hC : 0 < gaussianMR6FifthsConductor := by norm_num only [gaussianMR6FifthsConductor]
  have harg :
    0 ≤
      gaussianMR6FifthsBeta ^ 2 +
        4 * gaussianMR6FifthsD * (gaussianMR6FifthsConductor * L + 18) := by
    have hL' : 0 ≤ L := by linarith only [hL]
    have hterm : 0 ≤ gaussianMR6FifthsConductor * L + 18 := by positivity
    positivity
  have hz :
    z ^ 2 =
      gaussianMR6FifthsBeta ^ 2 +
        4 * gaussianMR6FifthsD * (gaussianMR6FifthsConductor * L + 18) := by
    dsimp only [z]
    rw [Real.sq_sqrt harg]
  have hD0 : gaussianMR6FifthsD ≠ 0 := ne_of_gt hD
  have hlin : 2 * gaussianMR6FifthsD * gaussianMR18Root L = gaussianMR6FifthsBeta + z := by
    dsimp only [gaussianMR18Root, z]
    field_simp [hD0]
  calc
    gaussianMR6FifthsD * gaussianMR18Radius L =
        (4 * gaussianMR6FifthsD ^ 2 * gaussianMR18Root L ^ 2) / (4 * gaussianMR6FifthsD) :=
      by
      dsimp only [gaussianMR18Radius]
      field_simp [hD0]
    _ = (gaussianMR6FifthsBeta + z) ^ 2 / (4 * gaussianMR6FifthsD) := by
      rw [← hlin]
      ring
    _ =
        (gaussianMR6FifthsBeta ^ 2 + 2 * gaussianMR6FifthsBeta * z + z ^ 2) /
          (4 * gaussianMR6FifthsD) :=
      by ring
    _ =
        (2 * gaussianMR6FifthsBeta ^ 2 + 2 * gaussianMR6FifthsBeta * z +
            4 * gaussianMR6FifthsD * (gaussianMR6FifthsConductor * L + 18)) /
          (4 * gaussianMR6FifthsD) :=
      by
      rw [hz]; ring
    _ =
        (2 * gaussianMR6FifthsBeta * (gaussianMR6FifthsBeta + z) +
            4 * gaussianMR6FifthsD * (gaussianMR6FifthsConductor * L + 18)) /
          (4 * gaussianMR6FifthsD) :=
      by ring
    _ =
        (2 * gaussianMR6FifthsBeta * (2 * gaussianMR6FifthsD * gaussianMR18Root L) +
            4 * gaussianMR6FifthsD * (gaussianMR6FifthsConductor * L + 18)) /
          (4 * gaussianMR6FifthsD) :=
      by rw [hlin]
    _ = gaussianMR6FifthsConductor * L + gaussianMR6FifthsBeta * gaussianMR18Root L + 18 := by
      field_simp [hD0]
      ring

/-- The leading and square-root coefficients in the 6/5 budget are positive. -/
theorem gaussianMR6Fifths_coefficients_pos :
    0 < gaussianMR6FifthsD ∧ 0 < gaussianMR6FifthsBeta := by
  constructor
  · norm_num only [gaussianMR6FifthsD, gaussianMR6FifthsIndex, gaussianMR6FifthsMass,
      gaussianMR6FifthsEndpoint]
  · norm_num only [gaussianMR6FifthsBeta, gaussianMR6FifthsIndex, gaussianMR6FifthsMass]

/-- The constant-18 root is at least 15 from logarithmic scale 300 onward. -/
theorem gaussianMR18Root_lower_15 {L : ℝ} (hL : 300 ≤ L) : 15 ≤ gaussianMR18Root L := by
  by_contra hnot
  have hlt : gaussianMR18Root L < 15 := lt_of_not_ge hnot
  have hEq := gaussianMR18Radius_equation hL
  have heq :
    gaussianMR6FifthsD * gaussianMR18Root L ^ 2 - gaussianMR6FifthsBeta * gaussianMR18Root L =
      gaussianMR6FifthsConductor * L + 18 := by
    dsimp only [gaussianMR18Radius] at hEq
    nlinarith only [hEq]
  have hmono : 0 < gaussianMR6FifthsD * (15 + gaussianMR18Root L) - gaussianMR6FifthsBeta := by
    have hbase : 0 < gaussianMR6FifthsD * 15 - gaussianMR6FifthsBeta := by
      norm_num only [gaussianMR6FifthsD, gaussianMR6FifthsIndex, gaussianMR6FifthsMass,
        gaussianMR6FifthsEndpoint, gaussianMR6FifthsBeta]
    nlinarith only [hbase, gaussianMR6Fifths_coefficients_pos.1, gaussianMR18Root_pos hL]
  have hfactor := mul_nonneg (sub_nonneg.mpr hlt.le) hmono.le
  have hpoly :
    gaussianMR6FifthsD * gaussianMR18Root L ^ 2 - gaussianMR6FifthsBeta * gaussianMR18Root L ≤
      gaussianMR6FifthsD * 225 - 15 * gaussianMR6FifthsBeta := by
    nlinarith only [hfactor]
  have hanchor :
    gaussianMR6FifthsD * 225 - 15 * gaussianMR6FifthsBeta - 300 * gaussianMR6FifthsConductor - 18 <
      0 := by
    norm_num only [gaussianMR6FifthsD, gaussianMR6FifthsIndex, gaussianMR6FifthsMass,
      gaussianMR6FifthsEndpoint, gaussianMR6FifthsBeta, gaussianMR6FifthsConductor]
  have hlower :
    300 * gaussianMR6FifthsConductor + 18 ≤
      gaussianMR6FifthsD * gaussianMR18Root L ^ 2 - gaussianMR6FifthsBeta * gaussianMR18Root L := by
    rw [heq]
    nlinarith only [hL,
      (show 0 < gaussianMR6FifthsConductor by norm_num only [gaussianMR6FifthsConductor])]
  linarith only [hpoly, hanchor, hlower]

/-- The constant-18 radius has the linear lower bound used in the error budget. -/
theorem gaussianMR18Radius_lower {L : ℝ} (hL : 300 ≤ L) :
    (5 / 8 : ℝ) * L + 40 ≤ gaussianMR18Radius L := by
  have hD := gaussianMR6Fifths_coefficients_pos.1
  have hB := gaussianMR6Fifths_coefficients_pos.2
  have hEq := gaussianMR18Radius_equation hL
  have hbase : gaussianMR6FifthsD * (5 / 8 : ℝ) ≤ gaussianMR6FifthsConductor := by
    norm_num only [gaussianMR6FifthsD, gaussianMR6FifthsIndex, gaussianMR6FifthsMass,
      gaussianMR6FifthsEndpoint, gaussianMR6FifthsConductor]
  have hconst : gaussianMR6FifthsD * 40 ≤ 15 * gaussianMR6FifthsBeta + 18 := by
    norm_num only [gaussianMR6FifthsD, gaussianMR6FifthsIndex, gaussianMR6FifthsMass,
      gaussianMR6FifthsEndpoint, gaussianMR6FifthsBeta]
  have hL0 : 0 ≤ L := by linarith only [hL]
  have hbaseL := mul_le_mul_of_nonneg_right hbase hL0
  have hlinear :
    gaussianMR6FifthsD * ((5 / 8 : ℝ) * L + 40) ≤
      gaussianMR6FifthsConductor * L + 15 * gaussianMR6FifthsBeta + 18 := by
    nlinarith only [hbaseL, hconst]
  have hmain :
    gaussianMR6FifthsD * ((5 / 8 : ℝ) * L + 40) ≤ gaussianMR6FifthsD * gaussianMR18Radius L := by
    calc
      gaussianMR6FifthsD * ((5 / 8 : ℝ) * L + 40) ≤
          gaussianMR6FifthsConductor * L + 15 * gaussianMR6FifthsBeta + 18 :=
        hlinear
      _ ≤ gaussianMR6FifthsConductor * L + gaussianMR6FifthsBeta * gaussianMR18Root L + 18 := by
        nlinarith only [hB, gaussianMR18Root_lower_15 hL]
      _ = gaussianMR6FifthsD * gaussianMR18Radius L := hEq.symm
  exact le_of_mul_le_mul_left hmain hD

/-- The constant-18 radius is at least 455/2 on its full range. -/
theorem gaussianMR18Radius_lower_455_over_2 {L : ℝ} (hL : 300 ≤ L) :
    455 / 2 ≤ gaussianMR18Radius L := by
  have hr := gaussianMR18Radius_lower hL
  nlinarith only [hr, hL]

/-- The constant-18 cutoff exceeds the 50000-prefix scale. -/
theorem gaussianMR18Bound_gt_prefix {L : ℝ} (hL : 300 ≤ L) : 50000 < gaussianMR18Bound L := by
  have hr := gaussianMR18Radius_lower_455_over_2 hL
  have hsum : 0 ≤ gaussianMR18Radius L + 455 / 2 := by linarith only [hr]
  have hfactor := mul_nonneg (sub_nonneg.mpr hr) hsum
  have hsq : (455 / 2 : ℝ) ^ 2 ≤ gaussianMR18Radius L ^ 2 := by nlinarith only [hfactor]
  have hscaled := mul_le_mul_of_nonneg_left hsq (by norm_num only : (0 : ℝ) ≤ 6 / 5)
  have hstrict : 50000 < (6 / 5 : ℝ) * (455 / 2) ^ 2 := by norm_num only
  change 50000 < (6 / 5 : ℝ) * gaussianMR18Radius L ^ 2
  linarith only [hstrict, hscaled]

/-- The constant-18 Gaussian bound absorbs the local `0.3 L²` envelope from
scale 300 onward. -/
theorem gaussianMR18Bound_gt_local_three_tenths {L : ℝ} (hL : 300 ≤ L) :
    (3 / 10 : ℝ) * L ^ 2 < gaussianMR18Bound L := by
  have hLpos : 0 < L := by linarith only [hL]
  have hr := gaussianMR18Radius_lower hL
  have hr' : (5 / 8 : ℝ) * L ≤ gaussianMR18Radius L := by linarith only [hr]
  have hsq := mul_self_le_mul_self (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 5 / 8) hLpos.le) hr'
  have hscale := mul_le_mul_of_nonneg_left hsq (by norm_num only : (0 : ℝ) ≤ 6 / 5)
  have hcoeff : (3 / 10 : ℝ) < (6 / 5) * (5 / 8) ^ 2 := by norm_num only
  have hstrict := mul_lt_mul_of_pos_right hcoeff (sq_pos_of_pos hLpos)
  dsimp only [gaussianMR18Bound] at hscale ⊢
  nlinarith only [hscale, hstrict]

/-- The constant-18 radius remains below a rational linear scale from its
starting point, with enough margin to put its bound below `0.7 L²`. -/
theorem gaussianMR18Radius_lt_7637_over_10000_scale {L : ℝ} (hL : 300 ≤ L) :
    gaussianMR18Radius L < (7637 / 10000 : ℝ) * L := by
  let R0 := (7637 / 10000 : ℝ) * L
  let s := gaussianMR18Root L
  let r := gaussianMR18Radius L
  let A :=
    (639999 / 1000000 : ℝ) * (7637 / 10000) - gaussianMR6FifthsConductor -
      (257 / 500 : ℝ) * (507 / 10000)
  have hLpos : 0 < L := by linarith only [hL]
  have hspos : 0 < s := gaussianMR18Root_pos hL
  have hsq : r = s ^ 2 := by dsimp only [r, gaussianMR18Radius, s]
  have hroot15 := gaussianMR18Root_lower_15 hL
  have hRpos : 0 < R0 := by
    dsimp only [R0]; positivity
  have hLprod : 300 * L ≤ L ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hL (le_of_lt hLpos)
    nlinarith only [hmul]
  have hR0upper : Real.sqrt R0 ≤ (507 / 10000 : ℝ) * L := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · dsimp only [R0]
      nlinarith only [hLprod]
  have hD : (639999 / 1000000 : ℝ) ≤ gaussianMR6FifthsD := by
    norm_num only [gaussianMR6FifthsD, gaussianMR6FifthsIndex, gaussianMR6FifthsMass,
      gaussianMR6FifthsEndpoint]
  have hBeta : gaussianMR6FifthsBeta ≤ (257 / 500 : ℝ) := by
    norm_num only [gaussianMR6FifthsBeta, gaussianMR6FifthsIndex, gaussianMR6FifthsMass]
  have hCon : gaussianMR6FifthsConductor = 161 / 400 := by
    norm_num only [gaussianMR6FifthsConductor]
  have hApos : 0 < A := by
    dsimp only [A]
    rw [hCon]
    norm_num only
  have hA300 : 0 < A * 300 - 18 := by
    dsimp only [A]
    rw [hCon]
    norm_num only
  have hlinear : 0 < A * L - 18 := by
    have hstep := mul_nonneg hApos.le (show 0 ≤ L - 300 by linarith only [hL])
    dsimp only [A] at hstep hA300 ⊢
    nlinarith only [hstep, hA300]
  have hmargin :
    0 <
      gaussianMR6FifthsD * R0 - gaussianMR6FifthsConductor * L -
        gaussianMR6FifthsBeta * Real.sqrt R0 -
        18 := by
    have hDscaled := mul_le_mul_of_nonneg_right hD (le_of_lt hRpos)
    have hbetascaled :=
      mul_le_mul hBeta hR0upper (Real.sqrt_nonneg R0) (by norm_num only : (0 : ℝ) ≤ 257 / 500)
    have hbase :
      0 <
        (639999 / 1000000 : ℝ) * (7637 / 10000) * L - gaussianMR6FifthsConductor * L -
          (257 / 500 : ℝ) * (507 / 10000) * L -
          18 := by
      calc
        0 < A * L - 18 := hlinear
        _ =
            (639999 / 1000000 : ℝ) * (7637 / 10000) * L - gaussianMR6FifthsConductor * L -
              (257 / 500 : ℝ) * (507 / 10000) * L -
              18 :=
          by
          dsimp only [A]
          rw [hCon]
          ring
    dsimp only [R0] at hDscaled hbetascaled ⊢
    nlinarith only [hDscaled, hbetascaled, hbase]
  have hEq := gaussianMR18Radius_equation hL
  have hfactorpos : 0 < gaussianMR6FifthsD - gaussianMR6FifthsBeta / (Real.sqrt R0 + s) := by
    have hsum : 15 ≤ Real.sqrt R0 + s := by
      have hsqrt0 : 0 ≤ Real.sqrt R0 := Real.sqrt_nonneg _
      linarith only [hsqrt0, hroot15]
    have hmul : (639999 / 1000000 : ℝ) * 15 ≤ gaussianMR6FifthsD * (Real.sqrt R0 + s) := by
      calc
        (639999 / 1000000 : ℝ) * 15 ≤ gaussianMR6FifthsD * 15 := by nlinarith only [hD]
        _ ≤ gaussianMR6FifthsD * (Real.sqrt R0 + s) :=
          mul_le_mul_of_nonneg_left hsum gaussianMR6Fifths_coefficients_pos.1.le
    have hquot : gaussianMR6FifthsBeta / (Real.sqrt R0 + s) < gaussianMR6FifthsD :=
      (div_lt_iff₀ (by linarith only [hsum])).2 (by nlinarith only [hmul, hBeta])
    exact sub_pos.mpr hquot
  have hsumpos : 0 < Real.sqrt R0 + s := add_pos (Real.sqrt_pos.2 hRpos) hspos
  have hsqrtSq : (Real.sqrt R0) ^ 2 = R0 := Real.sq_sqrt hRpos.le
  have hsqrtDiff : Real.sqrt R0 - s = (R0 - s ^ 2) / (Real.sqrt R0 + s) := by
    field_simp [hsumpos.ne']
    nlinarith only [hsqrtSq]
  have hidentity :
    gaussianMR6FifthsD * R0 - gaussianMR6FifthsConductor * L -
        gaussianMR6FifthsBeta * Real.sqrt R0 -
        18 -
        (gaussianMR6FifthsD * r - gaussianMR6FifthsConductor * L - gaussianMR6FifthsBeta * s - 18) =
      (R0 - r) * (gaussianMR6FifthsD - gaussianMR6FifthsBeta / (Real.sqrt R0 + s)) := by
    rw [hsq]
    calc
      _ = gaussianMR6FifthsD * (R0 - s ^ 2) - gaussianMR6FifthsBeta * (Real.sqrt R0 - s) := by ring
      _ = (R0 - s ^ 2) * (gaussianMR6FifthsD - gaussianMR6FifthsBeta / (Real.sqrt R0 + s)) := by
        rw [hsqrtDiff]
        ring
  have hactual :
    gaussianMR6FifthsD * r - gaussianMR6FifthsConductor * L - gaussianMR6FifthsBeta * s - 18 =
      0 := by
    dsimp only [r, s]
    linarith only [hEq]
  have hdiffpos : 0 < R0 - r := by
    by_contra hnot
    have hle : R0 - r ≤ 0 := le_of_not_gt hnot
    have hprod : (R0 - r) * (gaussianMR6FifthsD - gaussianMR6FifthsBeta / (Real.sqrt R0 + s)) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hle hfactorpos.le
    have hId := hidentity
    rw [hactual, sub_zero] at hId
    rw [hId] at hmargin
    exact (not_lt_of_ge hprod) hmargin
  have hout : r < R0 := by linarith only [hdiffpos]
  dsimp only [r, R0] at hout ⊢
  exact hout

/-- The constant-18 Gaussian cutoff is strictly below `0.7 L²` throughout
its full range beginning at logarithmic scale 300. -/
theorem gaussianMR18Bound_lt_sevenTenths_sq {L : ℝ} (hL : 300 ≤ L) :
    gaussianMR18Bound L < (7 / 10 : ℝ) * L ^ 2 := by
  have hrad := gaussianMR18Radius_lt_7637_over_10000_scale hL
  have hLpos : 0 < L := by linarith only [hL]
  have hrpos : 0 < gaussianMR18Radius L := by
    have hlow := gaussianMR18Radius_lower hL
    nlinarith only [hlow, hL]
  have hsq : gaussianMR18Radius L ^ 2 < ((7637 / 10000 : ℝ) * L) ^ 2 :=
    (sq_lt_sq₀ hrpos.le (mul_nonneg (by norm_num only) hLpos.le)).2 hrad
  have hscaled := mul_lt_mul_of_pos_left hsq (by norm_num only : (0 : ℝ) < 6 / 5)
  have hcoeff : (6 / 5 : ℝ) * (7637 / 10000) ^ 2 < 7 / 10 := by norm_num only
  have hcoeffL := mul_lt_mul_of_pos_right hcoeff (sq_pos_of_pos hLpos)
  dsimp only [gaussianMR18Bound] at hscaled ⊢
  nlinarith only [hscaled, hcoeffL]

/-- The root discriminant is nonnegative for logarithmic scales at least 500. -/
theorem gaussianMR6Fifths_discriminant_nonneg {L : ℝ} (hL : 500 ≤ L) :
    0 ≤
      gaussianMR6FifthsBeta ^ 2 +
        4 * gaussianMR6FifthsD * (gaussianMR6FifthsConductor * L + 29) := by
  obtain ⟨hD, hBeta⟩ := gaussianMR6Fifths_coefficients_pos
  have hC : 0 < gaussianMR6FifthsConductor := by norm_num only [gaussianMR6FifthsConductor]
  have harg : 0 < gaussianMR6FifthsConductor * L + 29 := by nlinarith only [hL, hC]
  exact
    add_nonneg (sq_nonneg gaussianMR6FifthsBeta)
      (mul_nonneg (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 4) hD.le) harg.le)

/-- The 6/5 budget root is positive on its stated logarithmic range. -/
theorem gaussianMR6FifthsRoot_pos {L : ℝ} (_hL : 500 ≤ L) : 0 < gaussianMR6FifthsRoot L := by
  obtain ⟨hD, hBeta⟩ := gaussianMR6Fifths_coefficients_pos
  have hnum :
    0 <
      gaussianMR6FifthsBeta +
        Real.sqrt
          (gaussianMR6FifthsBeta ^ 2 +
            4 * gaussianMR6FifthsD * (gaussianMR6FifthsConductor * L + 29)) :=
    add_pos_of_pos_of_nonneg hBeta (Real.sqrt_nonneg _)
  have hden : 0 < 2 * gaussianMR6FifthsD := by exact mul_pos (by norm_num only : (0 : ℝ) < 2) hD
  dsimp only [gaussianMR6FifthsRoot]
  exact div_pos hnum hden

/-- The defined radius satisfies the quadratic equation for the 6/5 budget. -/
theorem gaussianMR6FifthsRadius_equation {L : ℝ} (hL : 500 ≤ L) :
    gaussianMR6FifthsD * gaussianMR6FifthsRadius L =
      gaussianMR6FifthsConductor * L + gaussianMR6FifthsBeta * gaussianMR6FifthsRoot L + 29 := by
  let z :=
    Real.sqrt
      (gaussianMR6FifthsBeta ^ 2 + 4 * gaussianMR6FifthsD * (gaussianMR6FifthsConductor * L + 29))
  have hD : 0 < gaussianMR6FifthsD := gaussianMR6Fifths_coefficients_pos.1
  have harg := gaussianMR6Fifths_discriminant_nonneg hL
  have hz :
    z ^ 2 =
      gaussianMR6FifthsBeta ^ 2 +
        4 * gaussianMR6FifthsD * (gaussianMR6FifthsConductor * L + 29) := by
    dsimp only [z]
    rw [Real.sq_sqrt harg]
  have hD0 : gaussianMR6FifthsD ≠ 0 := ne_of_gt hD
  have hlin : 2 * gaussianMR6FifthsD * gaussianMR6FifthsRoot L = gaussianMR6FifthsBeta + z := by
    dsimp only [gaussianMR6FifthsRoot, z]
    field_simp
  calc
    gaussianMR6FifthsD * gaussianMR6FifthsRadius L =
        (4 * gaussianMR6FifthsD ^ 2 * gaussianMR6FifthsRoot L ^ 2) / (4 * gaussianMR6FifthsD) :=
      by
      dsimp only [gaussianMR6FifthsRadius]
      field_simp
    _ = (gaussianMR6FifthsBeta + z) ^ 2 / (4 * gaussianMR6FifthsD) := by
      rw [← hlin]
      ring
    _ =
        (gaussianMR6FifthsBeta ^ 2 + 2 * gaussianMR6FifthsBeta * z + z ^ 2) /
          (4 * gaussianMR6FifthsD) :=
      by ring
    _ =
        (2 * gaussianMR6FifthsBeta ^ 2 + 2 * gaussianMR6FifthsBeta * z +
            4 * gaussianMR6FifthsD * (gaussianMR6FifthsConductor * L + 29)) /
          (4 * gaussianMR6FifthsD) :=
      by
      rw [hz]; ring
    _ =
        (2 * gaussianMR6FifthsBeta * (gaussianMR6FifthsBeta + z) +
            4 * gaussianMR6FifthsD * (gaussianMR6FifthsConductor * L + 29)) /
          (4 * gaussianMR6FifthsD) :=
      by ring
    _ =
        (2 * gaussianMR6FifthsBeta * (2 * gaussianMR6FifthsD * gaussianMR6FifthsRoot L) +
            4 * gaussianMR6FifthsD * (gaussianMR6FifthsConductor * L + 29)) /
          (4 * gaussianMR6FifthsD) :=
      by rw [hlin]
    _ = gaussianMR6FifthsConductor * L + gaussianMR6FifthsBeta * gaussianMR6FifthsRoot L + 29 := by
      field_simp
      ring

/-- The constant-18 candidate is strictly below the existing 6/5 bound on
the common range. -/
theorem gaussianMR18Bound_lt_gaussianMR6FifthsBound {L : ℝ} (hL : 500 ≤ L) :
    gaussianMR18Bound L < gaussianMR6FifthsBound L := by
  let s := gaussianMR18Root L
  let t := gaussianMR6FifthsRoot L
  have hs : 0 < s := gaussianMR18Root_pos (by linarith only [hL])
  have ht : 0 < t := gaussianMR6FifthsRoot_pos hL
  have hs15 : 15 ≤ s := gaussianMR18Root_lower_15 (by linarith only [hL])
  have hD := gaussianMR6Fifths_coefficients_pos.1
  have hEq18 := gaussianMR18Radius_equation (by linarith only [hL])
  have hEq6 := gaussianMR6FifthsRadius_equation hL
  dsimp only [s, gaussianMR18Radius] at hEq18
  dsimp only [t, gaussianMR6FifthsRadius] at hEq6
  have hbase : gaussianMR6FifthsBeta < gaussianMR6FifthsD * 15 := by
    norm_num only [gaussianMR6FifthsBeta, gaussianMR6FifthsD, gaussianMR6FifthsIndex,
      gaussianMR6FifthsMass, gaussianMR6FifthsEndpoint]
  have hsum : 0 < gaussianMR6FifthsD * (s + t) - gaussianMR6FifthsBeta := by
    have hrootSum : 15 ≤ s + t := by linarith only [hs15, ht]
    have hmul := mul_le_mul_of_nonneg_left hrootSum hD.le
    nlinarith only [hbase, hmul]
  have hprod : (t - s) * (gaussianMR6FifthsD * (t + s) - gaussianMR6FifthsBeta) = 11 := by
    nlinarith only [hEq18, hEq6]
  have hdiff : s < t := by
    by_contra hnot
    have hle : t ≤ s := le_of_not_gt hnot
    have hsum' : 0 ≤ gaussianMR6FifthsD * (t + s) - gaussianMR6FifthsBeta := by
      simpa only [add_comm] using hsum.le
    have hnonpos : (t - s) * (gaussianMR6FifthsD * (t + s) - gaussianMR6FifthsBeta) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hle) hsum'
    linarith only [hprod, hnonpos]
  have hradFactor := mul_pos (sub_pos.mpr hdiff) (by nlinarith only [hs, hdiff] : 0 < t + s)
  have hradSq : s ^ 2 < t ^ 2 := by nlinarith only [hradFactor]
  have hrad : gaussianMR18Radius L < gaussianMR6FifthsRadius L := by
    dsimp only [gaussianMR18Radius, gaussianMR6FifthsRadius]
    exact hradSq
  have hsR : 0 < gaussianMR18Radius L := by
    dsimp only [gaussianMR18Radius]
    exact sq_pos_of_pos hs
  have htR : 0 < gaussianMR6FifthsRadius L := by
    dsimp only [gaussianMR6FifthsRadius]
    exact sq_pos_of_pos ht
  have hpowFactor := mul_pos (sub_pos.mpr hrad) (by linarith only [hsR, htR])
  have hpow : gaussianMR18Radius L ^ 2 < gaussianMR6FifthsRadius L ^ 2 := by
    nlinarith only [hpowFactor]
  have hscaled := mul_lt_mul_of_pos_left hpow (by norm_num only : (0 : ℝ) < 6 / 5)
  simpa only [gaussianMR18Bound, gaussianMR6FifthsBound] using hscaled

/-- The 6/5 radius is at least five eighths of the logarithmic scale. -/
theorem gaussianMR6FifthsRadius_lower {L : ℝ} (hL : 500 ≤ L) :
    (5 / 8 : ℝ) * L ≤ gaussianMR6FifthsRadius L := by
  obtain ⟨hD, hBeta⟩ := gaussianMR6Fifths_coefficients_pos
  have hRoot := gaussianMR6FifthsRoot_pos hL
  have hEq := gaussianMR6FifthsRadius_equation hL
  have hLpos : 0 < L := by linarith only [hL]
  have hstrict :
    gaussianMR6FifthsConductor * L < gaussianMR6FifthsD * gaussianMR6FifthsRadius L := by
    rw [hEq]
    have hrem : 0 < gaussianMR6FifthsBeta * gaussianMR6FifthsRoot L + 29 := by
      exact add_pos (mul_pos hBeta hRoot) (by norm_num only)
    linarith only [hrem]
  have hcoeff : gaussianMR6FifthsD * (5 / 8 : ℝ) < gaussianMR6FifthsConductor := by
    norm_num only [gaussianMR6FifthsD, gaussianMR6FifthsIndex, gaussianMR6FifthsMass,
      gaussianMR6FifthsEndpoint, gaussianMR6FifthsConductor]
  have hscaled := mul_lt_mul_of_pos_right hcoeff hLpos
  by_contra hnot
  have hlt : gaussianMR6FifthsRadius L < (5 / 8 : ℝ) * L := lt_of_not_ge hnot
  have hrad := mul_lt_mul_of_pos_left hlt hD
  nlinarith only [hstrict, hscaled, hrad]

/-- The proposed witness bound dominates the existing 0.282924 L^2 branch. -/
theorem gaussianMR6FifthsBound_lower {L : ℝ} (hL : 500 ≤ L) :
    (282924 / 1000000 : ℝ) * L ^ 2 < gaussianMR6FifthsBound L := by
  have hLpos : 0 < L := by linarith only [hL]
  have hr := gaussianMR6FifthsRadius_lower hL
  have hsquare := mul_self_le_mul_self (mul_nonneg (by norm_num only) hLpos.le) hr
  have hscale := mul_le_mul_of_nonneg_left hsquare (by norm_num only : (0 : ℝ) ≤ 6 / 5)
  have hcoef : (282924 / 1000000 : ℝ) < (6 / 5) * (5 / 8) ^ 2 := by norm_num only
  have hstrict := mul_lt_mul_of_pos_right hcoef (sq_pos_of_pos hLpos)
  dsimp only [gaussianMR6FifthsBound, gaussianMR6FifthsRadius] at hscale ⊢
  nlinarith only [hscale, hstrict]

/-- The ambient Gaussian remainder is below 27 at the 6/5 radius. -/
theorem gaussianMR6Fifths_ambient_error_le {q : ℕ} {L : ℝ} (hL : 500 ≤ L) (hq : Real.log q ≤ L) :
    LLS.PaperStatements.gaussianAmbientError q (gaussianMR6FifthsRadius L ^ 2) ≤ 27 := by
  let r := gaussianMR6FifthsRadius L
  have hrL : (5 / 8 : ℝ) * L ≤ r := gaussianMR6FifthsRadius_lower hL
  have hLpos : 0 < L := by linarith only [hL]
  have hrpos : 0 < r := by
    have hscaled := mul_pos (by norm_num only : (0 : ℝ) < 5 / 8) hLpos
    exact lt_of_lt_of_le hscaled hrL
  have hsqrt : Real.sqrt (r ^ 2) = r := Real.sqrt_sq hrpos.le
  have hx : (2 : ℝ) ^ 16 ≤ r ^ 2 := by
    have hr312 : 312 ≤ r := by nlinarith only [hL, hrL]
    norm_num only at hr312 ⊢
    nlinarith only [hr312]
  have hdec :=
    LLS.PaperStatements.rpow_neg_nine_sixteenths_le_div_scale_sqrt (a := 2) (by norm_num only) hx
  have hP : (2129 / 2000 : ℝ) * (((7 / 6) * Real.log q + 4) / r) ≤ 21 / 10 := by
    rw [div_eq_mul_inv]
    field_simp [hrpos.ne']
    nlinarith only [hL, hq, hrL]
  have hC : 0 ≤ (11 / 10 : ℝ) * ((16 / 5) * (Real.log q + 283) + 5 / 3) := by
    have hlog := Real.log_natCast_nonneg q
    positivity
  have hb := mul_le_mul_of_nonneg_left hdec hC
  have hB : (11 / 10 : ℝ) * ((16 / 5) * (Real.log q + 283) + 5 / 3) / (2 * r) ≤ 9 / 2 := by
    rw [div_le_iff₀ (mul_pos (by norm_num only) hrpos)]
    nlinarith only [hL, hq, hrL]
  rw [hsqrt] at hb
  have hb' :
    (11 / 10 : ℝ) * (r ^ 2) ^ (-9 / 16 : ℝ) * ((16 / 5) * (Real.log q + 283) + 5 / 3) ≤
      (11 / 10 : ℝ) * ((16 / 5) * (Real.log q + 283) + 5 / 3) / (2 * r) := by
    simp only [div_eq_mul_inv] at hb hB ⊢
    nlinarith only [hb, hB]
  have hb'' := hb'.trans hB
  change LLS.PaperStatements.gaussianAmbientError q (r ^ 2) ≤ 27
  dsimp only [LLS.PaperStatements.gaussianAmbientError]
  rw [hsqrt]
  have htotal : (12871 / 1000 : ℝ) + 64 / 9 + 21 / 10 + 9 / 2 ≤ 27 := by norm_num only
  calc
    _ =
        (12871 / 1000 : ℝ) + 64 / 9 +
          ((2129 / 2000 : ℝ) * (((7 / 6) * Real.log q + 4) / r) +
            (11 / 10 : ℝ) * (r ^ 2) ^ (-9 / 16 : ℝ) * ((16 / 5) * (Real.log q + 283) + 5 / 3)) :=
      by ring
    _ =
        ((12871 / 1000 : ℝ) + 64 / 9 + (2129 / 2000 : ℝ) * (((7 / 6) * Real.log q + 4) / r)) +
          (11 / 10 : ℝ) * (r ^ 2) ^ (-9 / 16 : ℝ) * ((16 / 5) * (Real.log q + 283) + 5 / 3) :=
      by ring
    _ ≤ ((12871 / 1000 : ℝ) + 64 / 9 + 21 / 10) + 9 / 2 := by
      exact add_le_add (add_le_add_right hP ((12871 / 1000 : ℝ) + 64 / 9)) hb''
    _ = (12871 / 1000 : ℝ) + 64 / 9 + 21 / 10 + 9 / 2 := by ring
    _ ≤ 27 := htotal

/-- For index at least 10^9, the normalized index factors are bounded by
their values at 10^9 for the 6/5 mass and endpoint. -/
theorem gaussianMR6Fifths_index_coefficients {m : ℝ} (hm : gaussianMR6FifthsIndex ≤ m) :
    gaussianMR6FifthsD ≤ (m * gaussianMR6FifthsMass - gaussianMR6FifthsEndpoint) / (m - 1) ∧
      m / (m - 1) ≤ gaussianMR6FifthsIndex / (gaussianMR6FifthsIndex - 1) ∧
      (m / (m - 1)) * (gaussianMR6FifthsMass / 3 + 3 / 10) ≤ gaussianMR6FifthsBeta := by
  have hK : (1 : ℝ) < gaussianMR6FifthsIndex := by norm_num only [gaussianMR6FifthsIndex]
  have hden : 0 < m - 1 := by linarith only [hm, hK]
  have hKden : 0 < gaussianMR6FifthsIndex - 1 := by linarith only [hK]
  have hgamma : m / (m - 1) ≤ gaussianMR6FifthsIndex / (gaussianMR6FifthsIndex - 1) := by
    rw [div_le_div_iff₀ hden hKden]
    norm_num only [gaussianMR6FifthsIndex] at hm ⊢
    nlinarith only [hm]
  have hbase : 0 ≤ gaussianMR6FifthsMass / 3 + 3 / 10 := by norm_num only [gaussianMR6FifthsMass]
  refine ⟨?_, hgamma, ?_⟩
  · dsimp only [gaussianMR6FifthsD]
    rw [div_le_div_iff₀ hKden hden]
    norm_num only [gaussianMR6FifthsIndex, gaussianMR6FifthsMass, gaussianMR6FifthsEndpoint] at hm ⊢
    nlinarith only [hm]
  · dsimp only [gaussianMR6FifthsBeta]
    calc
      _ ≤
          (gaussianMR6FifthsIndex / (gaussianMR6FifthsIndex - 1)) *
            (gaussianMR6FifthsMass / 3 + 3 / 10) :=
        mul_le_mul_of_nonneg_right hgamma hbase
      _ = gaussianMR6FifthsBeta := by rfl

/-- The residual endpoint, inverse-radius, and ambient errors fit below 29
for the 6/5 branch at every index at least 10^9. -/
theorem gaussianMR6Fifths_scalar_error_lt {m s r A : ℝ} (hm : gaussianMR6FifthsIndex ≤ m)
    (hs : 17 ≤ s) (hr : 625 / 2 ≤ r)
    (hgamma : m / (m - 1) ≤ gaussianMR6FifthsIndex / (gaussianMR6FifthsIndex - 1)) (hA : A ≤ 27) :
    (m / (m - 1)) *
          (63 * gaussianMR6FifthsEndpoint / (10 * s) +
            1839 * gaussianMR6FifthsEndpoint / (1000 * r)) +
        13 / (m - 1) +
        A <
      29 := by
  have hK : (1 : ℝ) < gaussianMR6FifthsIndex := by norm_num only [gaussianMR6FifthsIndex]
  have hK0 : 0 ≤ gaussianMR6FifthsIndex := le_of_lt (by norm_num only [gaussianMR6FifthsIndex])
  have hmden : 0 < m - 1 := by linarith only [hm, hK]
  have hKden : 0 < gaussianMR6FifthsIndex - 1 := by norm_num only [gaussianMR6FifthsIndex]
  have hspos : 0 < s := by linarith only [hs]
  have hrpos : 0 < r := by linarith only [hr]
  have hnum1 : 0 ≤ 63 * gaussianMR6FifthsEndpoint / 10 := by
    norm_num only [gaussianMR6FifthsEndpoint]
  have hterm1 :
    (63 * gaussianMR6FifthsEndpoint / 10) / s ≤ (63 * gaussianMR6FifthsEndpoint / 10) / 17 :=
    div_le_div_of_nonneg_left hnum1 (by norm_num only) (by linarith only [hs])
  have hnum2 : 0 ≤ 1839 * gaussianMR6FifthsEndpoint / 1000 := by
    norm_num only [gaussianMR6FifthsEndpoint]
  have hterm2 :
    (1839 * gaussianMR6FifthsEndpoint / 1000) / r ≤
      (1839 * gaussianMR6FifthsEndpoint / 1000) / (625 / 2) :=
    div_le_div_of_nonneg_left hnum2 (by norm_num only) (by linarith only [hr])
  have htail := add_le_add hterm1 hterm2
  have hratio0 : 0 ≤ m / (m - 1) := div_nonneg (by linarith only [hm, hK0]) hmden.le
  have htailbound0 :
    0 ≤
      (63 * gaussianMR6FifthsEndpoint / 10) / 17 +
        (1839 * gaussianMR6FifthsEndpoint / 1000) / (625 / 2) := by
    positivity
  have htailK :
    (m / (m - 1)) *
        ((63 * gaussianMR6FifthsEndpoint / 10) / s +
          (1839 * gaussianMR6FifthsEndpoint / 1000) / r) ≤
      (gaussianMR6FifthsIndex / (gaussianMR6FifthsIndex - 1)) *
        ((63 * gaussianMR6FifthsEndpoint / 10) / 17 +
          (1839 * gaussianMR6FifthsEndpoint / 1000) / (625 / 2)) := by
    calc
      _ ≤
          (m / (m - 1)) *
            ((63 * gaussianMR6FifthsEndpoint / 10) / 17 +
              (1839 * gaussianMR6FifthsEndpoint / 1000) / (625 / 2)) :=
        mul_le_mul_of_nonneg_left htail hratio0
      _ ≤ _ := mul_le_mul_of_nonneg_right hgamma htailbound0
  have hconst : 13 / (m - 1) ≤ 13 / (gaussianMR6FifthsIndex - 1) := by
    apply div_le_div_of_nonneg_left
    · norm_num only
    · exact hKden
    · linarith only [hm]
  have htermEq :
    63 * gaussianMR6FifthsEndpoint / (10 * s) + 1839 * gaussianMR6FifthsEndpoint / (1000 * r) =
      (63 * gaussianMR6FifthsEndpoint / 10) / s +
        (1839 * gaussianMR6FifthsEndpoint / 1000) / r := by
    field_simp
  rw [htermEq]
  norm_num only [gaussianMR6FifthsIndex, gaussianMR6FifthsEndpoint] at htailK hconst ⊢
  nlinarith only [hA, htailK, hconst]

/-- After the 50000-prefix gain, the constant-18 inverse-radius and ambient
errors fit below 18 for every index at least 10^9. -/
theorem gaussianMR18_scalar_error_lt {m s r A : ℝ} (hm : gaussianMR6FifthsIndex ≤ m) (hs : 15 ≤ s)
    (hr : 455 / 2 ≤ r)
    (hgamma : m / (m - 1) ≤ gaussianMR6FifthsIndex / (gaussianMR6FifthsIndex - 1))
    (hA : A ≤ 27 - 484381 / 50000) :
    (m / (m - 1)) *
          (63 * gaussianMR6FifthsEndpoint / (10 * s) +
            1839 * gaussianMR6FifthsEndpoint / (1000 * r)) +
        13 / (m - 1) +
        A <
      18 := by
  have hK : (1 : ℝ) < gaussianMR6FifthsIndex := by norm_num only [gaussianMR6FifthsIndex]
  have hK0 : 0 ≤ gaussianMR6FifthsIndex := le_of_lt (by norm_num only [gaussianMR6FifthsIndex])
  have hmden : 0 < m - 1 := by linarith only [hm, hK]
  have hKden : 0 < gaussianMR6FifthsIndex - 1 := by norm_num only [gaussianMR6FifthsIndex]
  have hspos : 0 < s := by linarith only [hs]
  have hrpos : 0 < r := by linarith only [hr]
  have hnum1 : 0 ≤ 63 * gaussianMR6FifthsEndpoint / 10 := by
    norm_num only [gaussianMR6FifthsEndpoint]
  have hterm1 :
    (63 * gaussianMR6FifthsEndpoint / 10) / s ≤ (63 * gaussianMR6FifthsEndpoint / 10) / 15 :=
    div_le_div_of_nonneg_left hnum1 (by norm_num only) (by linarith only [hs])
  have hnum2 : 0 ≤ 1839 * gaussianMR6FifthsEndpoint / 1000 := by
    norm_num only [gaussianMR6FifthsEndpoint]
  have hterm2 :
    (1839 * gaussianMR6FifthsEndpoint / 1000) / r ≤
      (1839 * gaussianMR6FifthsEndpoint / 1000) / (455 / 2) :=
    div_le_div_of_nonneg_left hnum2 (by norm_num only) (by linarith only [hr])
  have htail := add_le_add hterm1 hterm2
  have hratio0 : 0 ≤ m / (m - 1) := div_nonneg (by linarith only [hm, hK0]) hmden.le
  have htailbound0 :
    0 ≤
      (63 * gaussianMR6FifthsEndpoint / 10) / 15 +
        (1839 * gaussianMR6FifthsEndpoint / 1000) / (455 / 2) := by
    positivity
  have htailK :
    (m / (m - 1)) *
        ((63 * gaussianMR6FifthsEndpoint / 10) / s +
          (1839 * gaussianMR6FifthsEndpoint / 1000) / r) ≤
      (gaussianMR6FifthsIndex / (gaussianMR6FifthsIndex - 1)) *
        ((63 * gaussianMR6FifthsEndpoint / 10) / 15 +
          (1839 * gaussianMR6FifthsEndpoint / 1000) / (455 / 2)) := by
    calc
      _ ≤
          (m / (m - 1)) *
            ((63 * gaussianMR6FifthsEndpoint / 10) / 15 +
              (1839 * gaussianMR6FifthsEndpoint / 1000) / (455 / 2)) :=
        mul_le_mul_of_nonneg_left htail hratio0
      _ ≤ _ := mul_le_mul_of_nonneg_right hgamma htailbound0
  have hconst : 13 / (m - 1) ≤ 13 / (gaussianMR6FifthsIndex - 1) := by
    apply div_le_div_of_nonneg_left
    · norm_num only
    · exact hKden
    · linarith only [hm]
  have htermEq :
    63 * gaussianMR6FifthsEndpoint / (10 * s) + 1839 * gaussianMR6FifthsEndpoint / (1000 * r) =
      (63 * gaussianMR6FifthsEndpoint / 10) / s +
        (1839 * gaussianMR6FifthsEndpoint / 1000) / r := by
    field_simp [hspos.ne', hrpos.ne']
  rw [htermEq]
  norm_num only [gaussianMR6FifthsIndex, gaussianMR6FifthsEndpoint] at htailK hconst ⊢
  nlinarith only [hA, htailK, hconst]

/-- The endpoint, inverse-radius and improved signed ambient errors fit below
six at every index at least one billion under the B6 radius thresholds. -/
theorem gaussianMR6_scalar_error_lt {m s r A : ℝ} (hm : gaussianMR6FifthsIndex ≤ m) (hs : 14 ≤ s)
    (hr : 415 / 2 ≤ r)
    (hgamma : m / (m - 1) ≤ gaussianMR6FifthsIndex / (gaussianMR6FifthsIndex - 1))
    (hA : A ≤ 27 / 5) :
    (m / (m - 1)) *
          (63 * gaussianMR6FifthsEndpoint / (10 * s) +
            1839 * gaussianMR6FifthsEndpoint / (1000 * r)) +
        13 / (m - 1) +
        A <
      6 := by
  have hK : (1 : ℝ) < gaussianMR6FifthsIndex := by norm_num only [gaussianMR6FifthsIndex]
  have hK0 : 0 ≤ gaussianMR6FifthsIndex := le_of_lt (by norm_num only [gaussianMR6FifthsIndex])
  have hmden : 0 < m - 1 := by linarith only [hm, hK]
  have hKden : 0 < gaussianMR6FifthsIndex - 1 := by norm_num only [gaussianMR6FifthsIndex]
  have hspos : 0 < s := by linarith only [hs]
  have hrpos : 0 < r := by linarith only [hr]
  have hnum1 : 0 ≤ 63 * gaussianMR6FifthsEndpoint / 10 := by
    norm_num only [gaussianMR6FifthsEndpoint]
  have hterm1 :
    (63 * gaussianMR6FifthsEndpoint / 10) / s ≤ (63 * gaussianMR6FifthsEndpoint / 10) / 14 :=
    div_le_div_of_nonneg_left hnum1 (by norm_num only) (by linarith only [hs])
  have hnum2 : 0 ≤ 1839 * gaussianMR6FifthsEndpoint / 1000 := by
    norm_num only [gaussianMR6FifthsEndpoint]
  have hterm2 :
    (1839 * gaussianMR6FifthsEndpoint / 1000) / r ≤
      (1839 * gaussianMR6FifthsEndpoint / 1000) / (415 / 2) :=
    div_le_div_of_nonneg_left hnum2 (by norm_num only) (by linarith only [hr])
  have htail := add_le_add hterm1 hterm2
  have hratio0 : 0 ≤ m / (m - 1) := div_nonneg (by linarith only [hm, hK0]) hmden.le
  have htailbound0 :
    0 ≤
      (63 * gaussianMR6FifthsEndpoint / 10) / 14 +
        (1839 * gaussianMR6FifthsEndpoint / 1000) / (415 / 2) := by
    positivity
  have htailK :
    (m / (m - 1)) *
        ((63 * gaussianMR6FifthsEndpoint / 10) / s +
          (1839 * gaussianMR6FifthsEndpoint / 1000) / r) ≤
      (gaussianMR6FifthsIndex / (gaussianMR6FifthsIndex - 1)) *
        ((63 * gaussianMR6FifthsEndpoint / 10) / 14 +
          (1839 * gaussianMR6FifthsEndpoint / 1000) / (415 / 2)) := by
    calc
      _ ≤
          (m / (m - 1)) *
            ((63 * gaussianMR6FifthsEndpoint / 10) / 14 +
              (1839 * gaussianMR6FifthsEndpoint / 1000) / (415 / 2)) :=
        mul_le_mul_of_nonneg_left htail hratio0
      _ ≤ _ := mul_le_mul_of_nonneg_right hgamma htailbound0
  have hconst : 13 / (m - 1) ≤ 13 / (gaussianMR6FifthsIndex - 1) := by
    apply div_le_div_of_nonneg_left
    · norm_num only
    · exact hKden
    · linarith only [hm]
  have htermEq :
    63 * gaussianMR6FifthsEndpoint / (10 * s) + 1839 * gaussianMR6FifthsEndpoint / (1000 * r) =
      (63 * gaussianMR6FifthsEndpoint / 10) / s +
        (1839 * gaussianMR6FifthsEndpoint / 1000) / r := by
    field_simp
  rw [htermEq]
  norm_num only [gaussianMR6FifthsIndex, gaussianMR6FifthsEndpoint] at htailK hconst ⊢
  nlinarith only [hA, htailK, hconst]

/-- The constant-18 root budget contradicts a normalized subgroup comparison
at every index at least 10^9 once the prefix gain is retained. -/
theorem gaussianMR18_large_index_comparison_impossible {m s r A L : ℝ}
    (hm : gaussianMR6FifthsIndex ≤ m) (hs : 15 ≤ s) (hr : 455 / 2 ≤ r)
    (hgamma : m / (m - 1) ≤ gaussianMR6FifthsIndex / (gaussianMR6FifthsIndex - 1))
    (hA : A ≤ 27 - 484381 / 50000)
    (hroot :
      gaussianMR6FifthsD * r = gaussianMR6FifthsConductor * L + gaussianMR6FifthsBeta * s + 18)
    (hcmp :
      gaussianMR6FifthsD * r ≤
        gaussianMR6FifthsConductor * L + gaussianMR6FifthsBeta * s +
          (m / (m - 1)) *
            (63 * gaussianMR6FifthsEndpoint / (10 * s) +
              1839 * gaussianMR6FifthsEndpoint / (1000 * r)) +
          13 / (m - 1) +
          A) :
    False := by
  have herr := gaussianMR18_scalar_error_lt hm hs hr hgamma hA
  have hspos : 0 < s := by linarith only [hs]
  have hrpos : 0 < r := by linarith only [hr]
  have htermEq :
    63 * gaussianMR6FifthsEndpoint / (10 * s) + 1839 * gaussianMR6FifthsEndpoint / (1000 * r) =
      (63 * gaussianMR6FifthsEndpoint / 10) / s +
        (1839 * gaussianMR6FifthsEndpoint / 1000) / r := by
    field_simp [hspos.ne', hrpos.ne']
  rw [htermEq, hroot] at hcmp
  rw [htermEq] at herr
  have hle :
    18 ≤
      (m / (m - 1)) *
          ((63 * gaussianMR6FifthsEndpoint / 10) / s +
            (1839 * gaussianMR6FifthsEndpoint / 1000) / r) +
        13 / (m - 1) +
        A := by
    nlinarith only [hcmp]
  exact (not_le_of_gt herr) hle

/-- At the constant-18 radius, the prefix-adjusted ambient error fits the
large-index scalar budget from logarithmic scale 300. -/
theorem gaussianMR18_ambient_error_prefix_le {q : ℕ} {L : ℝ} (hL : 300 ≤ L) (hq : Real.log q ≤ L) :
    LLS.PaperStatements.gaussianAmbientErrorPrefix q (gaussianMR18Radius L ^ 2) ≤
      27 - 484381 / 50000 := by
  let r := gaussianMR18Radius L
  have hr := gaussianMR18Radius_lower hL
  have hrR : (5 / 8 : ℝ) * L + 40 ≤ r := by simpa only [r] using hr
  have hrad : 455 / 2 ≤ r := by simpa only [r] using gaussianMR18Radius_lower_455_over_2 hL
  have hLpos : 0 < L := by linarith only [hL]
  have hrpos : 0 < r := by linarith only [hrad]
  have hsqrt : Real.sqrt (r ^ 2) = r := Real.sqrt_sq hrpos.le
  have hx : (19 / 10 : ℝ) ^ 16 ≤ r ^ 2 := by
    norm_num only at hrad ⊢
    nlinarith only [hrad]
  have hdec :=
    LLS.PaperStatements.rpow_neg_nine_sixteenths_le_div_scale_sqrt (a := 19 / 10) (by norm_num only)
      hx
  have hP : (2129 / 2000 : ℝ) * (((7 / 6) * Real.log q + 4) / r) ≤ 2 := by
    rw [div_eq_mul_inv]
    field_simp [hrpos.ne']
    nlinarith only [hL, hq, hrR]
  have hC : 0 ≤ (16 / 5 : ℝ) * (Real.log q + 283) + 5 / 3 := by
    have hlog := Real.log_natCast_nonneg q
    positivity
  have hbSmall :
    (11 / 10 : ℝ) * (r ^ 2) ^ (-9 / 16 : ℝ) * ((16 / 5 : ℝ) * (Real.log q + 283) + 5 / 3) ≤
      (11 / 10 : ℝ) * ((16 / 5 : ℝ) * (Real.log q + 283) + 5 / 3) / ((19 / 10 : ℝ) * r) := by
    rw [hsqrt] at hdec
    have hmul :=
      mul_le_mul_of_nonneg_left hdec (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 11 / 10) hC)
    calc
      _ = ((11 / 10 : ℝ) * ((16 / 5 : ℝ) * (Real.log q + 283) + 5 / 3)) * (r ^ 2) ^ (-9 / 16 : ℝ) :=
        by ring
      _ ≤
          ((11 / 10 : ℝ) * ((16 / 5 : ℝ) * (Real.log q + 283) + 5 / 3)) *
            (1 / ((19 / 10 : ℝ) * r)) :=
        hmul
      _ = (11 / 10 : ℝ) * ((16 / 5 : ℝ) * (Real.log q + 283) + 5 / 3) / ((19 / 10 : ℝ) * r) := by
        ring
  have hB :
    (11 / 10 : ℝ) * ((16 / 5 : ℝ) * (Real.log q + 283) + 5 / 3) / ((19 / 10 : ℝ) * r) ≤ 24 / 5 := by
    rw [div_le_iff₀ (mul_pos (by norm_num only) hrpos)]
    nlinarith only [hL, hq, hrR]
  have hb := hbSmall.trans hB
  dsimp only [LLS.PaperStatements.gaussianAmbientErrorPrefix, r]
  have hsqrt' : Real.sqrt (gaussianMR18Radius L ^ 2) = r := by simpa only [r] using hsqrt
  rw [hsqrt']
  have htotal : (159169 / 50000 : ℝ) + 64 / 9 + 2 + 24 / 5 ≤ 27 - 484381 / 50000 := by norm_num only
  calc
    _ =
        (159169 / 50000 : ℝ) + 64 / 9 +
          ((2129 / 2000 : ℝ) * (((7 / 6) * Real.log q + 4) / r) +
            (11 / 10 : ℝ) * (r ^ 2) ^ (-9 / 16 : ℝ) *
              ((16 / 5 : ℝ) * (Real.log q + 283) + 5 / 3)) :=
      by ring
    _ ≤ (159169 / 50000 : ℝ) + 64 / 9 + 2 + 24 / 5 := by nlinarith only [hP, hb]
    _ ≤ 27 - 484381 / 50000 := htotal

/-- The 6/5 radius equation rules out the normalized relative comparison at
every subgroup index at least 10^9. -/
theorem gaussianMR6Fifths_large_index_comparison_impossible {m s r A L : ℝ}
    (hm : gaussianMR6FifthsIndex ≤ m) (hs : 17 ≤ s) (hr : 625 / 2 ≤ r)
    (hgamma : m / (m - 1) ≤ gaussianMR6FifthsIndex / (gaussianMR6FifthsIndex - 1)) (hA : A ≤ 27)
    (hroot :
      gaussianMR6FifthsD * r = gaussianMR6FifthsConductor * L + gaussianMR6FifthsBeta * s + 29)
    (hcmp :
      gaussianMR6FifthsD * r ≤
        gaussianMR6FifthsConductor * L + gaussianMR6FifthsBeta * s +
          (m / (m - 1)) *
            (63 * gaussianMR6FifthsEndpoint / (10 * s) +
              1839 * gaussianMR6FifthsEndpoint / (1000 * r)) +
          13 / (m - 1) +
          A) :
    False := by
  have herr := gaussianMR6Fifths_scalar_error_lt hm hs hr hgamma hA
  have htermEq :
    63 * gaussianMR6FifthsEndpoint / (10 * s) + 1839 * gaussianMR6FifthsEndpoint / (1000 * r) =
      (63 * gaussianMR6FifthsEndpoint / 10) / s +
        (1839 * gaussianMR6FifthsEndpoint / 1000) / r := by
    field_simp
  rw [htermEq, hroot] at hcmp
  rw [htermEq] at herr
  exact (not_le_of_gt herr) (by nlinarith only [hcmp])

/-- Convert the actual relative subgroup inequality to the 6/5 budget form.
The cutoff mass and endpoint enter through the shared normalized main-term estimate. -/
theorem gaussianMR6Fifths_relative_comparison_impossible {m t s r A L I E C h : ℝ}
    (hm : gaussianMR6FifthsIndex ≤ m) (ht : t = m - 1) (hs : 0 < s) (hs17 : 17 ≤ s) (hr : r = s ^ 2)
    (hrbound : 625 / 2 ≤ r) (hh : h = 1 / (3 * s)) (hh1 : h ≤ 1 / 2)
    (hI : gaussianMR6FifthsMass ≤ I) (hE : E ≤ gaussianMR6FifthsEndpoint) (hC : C / t ≤ L)
    (hA : A ≤ 27)
    (hcmp :
      (m * (1 - h) * I - E) * r ≤
        gaussianMR6FifthsConductor * C +
          m * (1 / (10 * h) + ((21 / (10 * h) + 1839 / 1000) / r) * E) +
          13 +
          t * A)
    (hroot :
      gaussianMR6FifthsD * r = gaussianMR6FifthsConductor * L + gaussianMR6FifthsBeta * s + 29) :
    False := by
  have hK : (1 : ℝ) < gaussianMR6FifthsIndex := by norm_num only [gaussianMR6FifthsIndex]
  have hm4 : 4 ≤ m := by
    have hKreal : (1000000000 : ℝ) ≤ m := by
      norm_num only [gaussianMR6FifthsIndex] at hm ⊢
      exact hm
    linarith only [hKreal]
  have hI0 : gaussianMR6FifthsMass ≤ I := hI
  have hE0 : E ≤ 2129 / 2000 := by
    dsimp only [gaussianMR6FifthsEndpoint] at hE ⊢
    exact hE
  have hcoeff := gaussianMR6Fifths_index_coefficients hm
  have hgamma := hcoeff.2.1
  have hD : gaussianMR6FifthsD ≤ (m * gaussianMR6FifthsMass - gaussianMR6FifthsEndpoint) / t := by
    simpa only [ht] using hcoeff.1
  have hbeta : (m / t) * (gaussianMR6FifthsMass / 3 + 3 / 10) ≤ gaussianMR6FifthsBeta := by
    simpa only [ht] using hcoeff.2.2
  have hfinish :
    gaussianMR6FifthsD * r ≤
        gaussianMR6FifthsConductor * L + gaussianMR6FifthsBeta * s +
          (m / t) *
            (63 * gaussianMR6FifthsEndpoint / (10 * s) +
              1839 * gaussianMR6FifthsEndpoint / (1000 * r)) +
          13 / t +
          A →
      False := by
    intro hbudget
    exact
      gaussianMR6Fifths_large_index_comparison_impossible hm hs17 hrbound hgamma hA hroot
        (by simpa only [ht] using hbudget)
  exact
    gaussianMR_relative_comparison_to_scalar hm4 ht hs hr hh hh1 hI0 hE0 hC
      (by norm_num only [gaussianMR6FifthsConductor]) hD hbeta hcmp hfinish

/-- The index-four comparison with conductor cost `2L` is incompatible with
the 6/5 radius at logarithmic scales at least 500. -/
theorem gaussianMR6Fifths_triple_comparison_impossible {L : ℝ} (hL : 500 ≤ L)
    (hcmp :
      ((4 * gaussianMR6FifthsMass - gaussianMR6FifthsEndpoint) / 3) * gaussianMR6FifthsRadius L ≤
        (161 / 600 : ℝ) * L +
          (4 / 3 : ℝ) * (gaussianMR6FifthsMass / 3 + 3 / 10) * gaussianMR6FifthsRoot L +
          33) :
    False := by
  let r := gaussianMR6FifthsRadius L
  let s := gaussianMR6FifthsRoot L
  have hrlo : (625 / 2 : ℝ) ≤ r := by
    dsimp only [r]
    have hrad := gaussianMR6FifthsRadius_lower hL
    nlinarith only [hrad, hL]
  have hspos : 0 < s := by
    dsimp only [s]
    exact gaussianMR6FifthsRoot_pos hL
  have hsSq : s ^ 2 = r := by dsimp only [s, r, gaussianMR6FifthsRadius]
  have hs17 : 17 ≤ s := by nlinarith only [hsSq, hrlo, hspos]
  have hsle : s ≤ r / 17 := by
    apply (le_div_iff₀ (by norm_num only : (0 : ℝ) < 17)).2
    nlinarith only [hsSq, hs17]
  have hroot := gaussianMR6FifthsRadius_equation hL
  have hc : gaussianMR6FifthsConductor = 161 / 400 := by norm_num only [gaussianMR6FifthsConductor]
  have hroot' :
    gaussianMR6FifthsD * r = gaussianMR6FifthsConductor * L + gaussianMR6FifthsBeta * s + 29 := by
    simpa only [r, s] using hroot
  rw [hc] at hroot'
  have hindexCmp :
    (((4 * gaussianMR6FifthsMass - gaussianMR6FifthsEndpoint) / 3) -
          (2 / 3 : ℝ) * gaussianMR6FifthsD) *
        r ≤
      ((4 / 3 : ℝ) * (gaussianMR6FifthsMass / 3 + 3 / 10) - (2 / 3 : ℝ) * gaussianMR6FifthsBeta) *
          s +
        41 / 3 := by
    change
      ((4 * gaussianMR6FifthsMass - gaussianMR6FifthsEndpoint) / 3) * r ≤
        (161 / 600 : ℝ) * L + (4 / 3 : ℝ) * (gaussianMR6FifthsMass / 3 + 3 / 10) * s + 33 at hcmp
    nlinarith only [hcmp, hroot']
  have hbetaDiff :
    0 <
      (4 / 3 : ℝ) * (gaussianMR6FifthsMass / 3 + 3 / 10) - (2 / 3 : ℝ) * gaussianMR6FifthsBeta := by
    norm_num [gaussianMR6FifthsBeta, gaussianMR6FifthsIndex, gaussianMR6FifthsMass]
  have hgap :
    (((4 * gaussianMR6FifthsMass - gaussianMR6FifthsEndpoint) / 3) -
          (2 / 3 : ℝ) * gaussianMR6FifthsD) -
        ((4 / 3 : ℝ) * (gaussianMR6FifthsMass / 3 + 3 / 10) - (2 / 3 : ℝ) * gaussianMR6FifthsBeta) /
          17 >
      0 := by
    norm_num [gaussianMR6FifthsD, gaussianMR6FifthsBeta, gaussianMR6FifthsIndex,
      gaussianMR6FifthsMass, gaussianMR6FifthsEndpoint, gaussianMR6FifthsConductor]
  have hmargin :
    (41 / 3 : ℝ) <
      (((4 * gaussianMR6FifthsMass - gaussianMR6FifthsEndpoint) / 3) -
            (2 / 3 : ℝ) * gaussianMR6FifthsD) *
          (625 / 2) -
        ((4 / 3 : ℝ) * (gaussianMR6FifthsMass / 3 + 3 / 10) - (2 / 3 : ℝ) * gaussianMR6FifthsBeta) *
          (625 / 34) := by
    norm_num [gaussianMR6FifthsD, gaussianMR6FifthsBeta, gaussianMR6FifthsIndex,
      gaussianMR6FifthsMass, gaussianMR6FifthsEndpoint, gaussianMR6FifthsConductor]
  have hstrict :
    (41 / 3 : ℝ) <
      (((4 * gaussianMR6FifthsMass - gaussianMR6FifthsEndpoint) / 3) -
            (2 / 3 : ℝ) * gaussianMR6FifthsD) *
          r -
        ((4 / 3 : ℝ) * (gaussianMR6FifthsMass / 3 + 3 / 10) - (2 / 3 : ℝ) * gaussianMR6FifthsBeta) *
          s := by
    have hscaled := mul_le_mul_of_nonneg_left hsle hbetaDiff.le
    have hlow := mul_le_mul_of_nonneg_left hrlo (le_of_lt hgap)
    nlinarith only [hscaled, hlow, hmargin]
  apply (not_le_of_gt hstrict)
  nlinarith only [hindexCmp]

/-- The constant-18 Gaussian budget contradicts the index-four comparison
with conductor cost `2L` once the prefix-adjusted residual is below 23. -/
theorem gaussianMR18_triple_comparison_impossible {L : ℝ} (hL : 300 ≤ L)
    (hcmp :
      ((4 * gaussianMR6FifthsMass - gaussianMR6FifthsEndpoint) / 3) * gaussianMR18Radius L ≤
        (161 / 600 : ℝ) * L +
          (4 / 3 : ℝ) * (gaussianMR6FifthsMass / 3 + 3 / 10) * gaussianMR18Root L +
          23) :
    False := by
  let r := gaussianMR18Radius L
  let s := gaussianMR18Root L
  have hrlo : 455 / 2 ≤ r := by
    dsimp only [r]
    exact gaussianMR18Radius_lower_455_over_2 hL
  have hspos : 0 < s := by
    dsimp only [s]
    exact gaussianMR18Root_pos hL
  have hsSq : s ^ 2 = r := by dsimp only [s, r, gaussianMR18Radius]
  have hs15 : 15 ≤ s := by
    dsimp only [s]
    exact gaussianMR18Root_lower_15 hL
  have hsle : s ≤ r / 15 := by
    apply (le_div_iff₀ (by norm_num only : (0 : ℝ) < 15)).2
    nlinarith only [hsSq, hs15]
  have hroot := gaussianMR18Radius_equation hL
  have hc : gaussianMR6FifthsConductor = 161 / 400 := by norm_num only [gaussianMR6FifthsConductor]
  have hroot' :
    gaussianMR6FifthsD * r = gaussianMR6FifthsConductor * L + gaussianMR6FifthsBeta * s + 18 := by
    simpa only [r, s] using hroot
  rw [hc] at hroot'
  have hindexCmp :
    (((4 * gaussianMR6FifthsMass - gaussianMR6FifthsEndpoint) / 3) -
          (2 / 3 : ℝ) * gaussianMR6FifthsD) *
        r ≤
      ((4 / 3 : ℝ) * (gaussianMR6FifthsMass / 3 + 3 / 10) - (2 / 3 : ℝ) * gaussianMR6FifthsBeta) *
          s +
        11 := by
    change
      ((4 * gaussianMR6FifthsMass - gaussianMR6FifthsEndpoint) / 3) * r ≤
        (161 / 600 : ℝ) * L + (4 / 3 : ℝ) * (gaussianMR6FifthsMass / 3 + 3 / 10) * s + 23 at hcmp
    nlinarith only [hcmp, hroot']
  have hbetaDiff :
    0 <
      (4 / 3 : ℝ) * (gaussianMR6FifthsMass / 3 + 3 / 10) - (2 / 3 : ℝ) * gaussianMR6FifthsBeta := by
    norm_num [gaussianMR6FifthsBeta, gaussianMR6FifthsIndex, gaussianMR6FifthsMass]
  have hgap :
    (((4 * gaussianMR6FifthsMass - gaussianMR6FifthsEndpoint) / 3) -
          (2 / 3 : ℝ) * gaussianMR6FifthsD) -
        ((4 / 3 : ℝ) * (gaussianMR6FifthsMass / 3 + 3 / 10) - (2 / 3 : ℝ) * gaussianMR6FifthsBeta) /
          15 >
      0 := by
    norm_num [gaussianMR6FifthsD, gaussianMR6FifthsBeta, gaussianMR6FifthsIndex,
      gaussianMR6FifthsMass, gaussianMR6FifthsEndpoint, gaussianMR6FifthsConductor]
  have hmargin :
    (11 : ℝ) <
      (((4 * gaussianMR6FifthsMass - gaussianMR6FifthsEndpoint) / 3) -
            (2 / 3 : ℝ) * gaussianMR6FifthsD) *
          (455 / 2) -
        ((4 / 3 : ℝ) * (gaussianMR6FifthsMass / 3 + 3 / 10) - (2 / 3 : ℝ) * gaussianMR6FifthsBeta) *
          (455 / 30) := by
    norm_num [gaussianMR6FifthsD, gaussianMR6FifthsBeta, gaussianMR6FifthsIndex,
      gaussianMR6FifthsMass, gaussianMR6FifthsEndpoint, gaussianMR6FifthsConductor]
  have hstrict :
    (11 : ℝ) <
      (((4 * gaussianMR6FifthsMass - gaussianMR6FifthsEndpoint) / 3) -
            (2 / 3 : ℝ) * gaussianMR6FifthsD) *
          r -
        ((4 / 3 : ℝ) * (gaussianMR6FifthsMass / 3 + 3 / 10) - (2 / 3 : ℝ) * gaussianMR6FifthsBeta) *
          s := by
    have hscaled := mul_le_mul_of_nonneg_left hsle hbetaDiff.le
    have hlow := mul_le_mul_of_nonneg_left hrlo (le_of_lt hgap)
    nlinarith only [hscaled, hlow, hmargin]
  apply (not_le_of_gt hstrict)
  nlinarith only [hindexCmp]

/-- From scale 600, the 6/5 Gaussian bound is at most 2601/2800 of the
classified star bound. -/
theorem gaussianMR6FifthsBound_lt_gaussianMRStarBound_ratio {L : ℝ} (hL : 600 ≤ L) :
    gaussianMR6FifthsBound L < (2601 / 2800 : ℝ) * gaussianMRStarBound L := by
  let q : ℝ := 51 / 40
  let r := gaussianMR6FifthsRadius L
  let s := gaussianMR6FifthsRoot L
  let R := gaussianMRStarRadius L
  let S := gaussianMRStarRoot L
  have hspos : 0 < s := gaussianMR6FifthsRoot_pos (by linarith only [hL])
  have hSpos : 0 < S := gaussianMRStarRoot_pos hL
  have hr : s ^ 2 = r := by dsimp only [s, r, gaussianMR6FifthsRadius]
  have hR : S ^ 2 = R := by dsimp only [S, R, gaussianMRStarRadius]
  have hRlo : 294 ≤ R := by
    have hrad := gaussianMRStarRadius_lower hL
    nlinarith only [hrad, hL]
  have hSlo : 17 ≤ S := by nlinarith only [hR, hRlo, hSpos]
  have hqpos : 0 ≤ q := by norm_num only [q]
  have hqrootSq : Real.sqrt q ^ 2 = q := Real.sq_sqrt hqpos
  have hqroot : Real.sqrt q ≤ 113 / 100 := by
    have hqrootNonneg := Real.sqrt_nonneg q
    norm_num only [q] at hqrootSq ⊢
    nlinarith only [hqrootSq, hqrootNonneg]
  have hD6 : 0 < gaussianMR6FifthsD := gaussianMR6Fifths_coefficients_pos.1
  have hBeta6 : 0 < gaussianMR6FifthsBeta := gaussianMR6Fifths_coefficients_pos.2
  have hDstar : 0 < gaussianMRStarD := gaussianMRStar_coefficients_pos.1
  have hBetastar : 0 < gaussianMRStarBeta := gaussianMRStar_coefficients_pos.2
  have hcoef : 0 < gaussianMR6FifthsD * q - gaussianMRStarD := by
    norm_num [q, gaussianMR6FifthsD, gaussianMR6FifthsIndex, gaussianMR6FifthsMass,
      gaussianMR6FifthsEndpoint, gaussianMRStarD, gaussianMRStarIndex, gaussianMRStarMass,
      gaussianMRStarEndpoint]
  have hgap :
    17 * (gaussianMR6FifthsD * q - gaussianMRStarD) >
      gaussianMR6FifthsBeta * (113 / 100) - gaussianMRStarBeta := by
    norm_num [q, gaussianMR6FifthsD, gaussianMR6FifthsIndex, gaussianMR6FifthsMass,
      gaussianMR6FifthsEndpoint, gaussianMR6FifthsBeta, gaussianMRStarD, gaussianMRStarIndex,
      gaussianMRStarMass, gaussianMRStarEndpoint, gaussianMRStarBeta]
  have hscalar :
    gaussianMR6FifthsD * q * R - gaussianMR6FifthsBeta * (113 / 100) * S >
      gaussianMRStarD * R - gaussianMRStarBeta * S := by
    have hinner :
      0 <
        (gaussianMR6FifthsD * q - gaussianMRStarD) * S -
          (gaussianMR6FifthsBeta * (113 / 100) - gaussianMRStarBeta) := by
      have hscaled := mul_le_mul_of_nonneg_left hSlo hcoef.le
      have hlower :
        gaussianMR6FifthsBeta * (113 / 100) - gaussianMRStarBeta <
          (gaussianMR6FifthsD * q - gaussianMRStarD) * S :=
        lt_of_lt_of_le (by linarith only [hgap]) hscaled
      linarith only [hlower]
    have hscaled := mul_pos hinner hSpos
    rw [← hR]
    nlinarith only [hscaled, hR]
  have hroot6 := gaussianMR6FifthsRadius_equation (by linarith only [hL])
  have hrootStar := gaussianMRStarRadius_equation hL
  have hroot6' :
    gaussianMR6FifthsD * r = gaussianMR6FifthsConductor * L + gaussianMR6FifthsBeta * s + 29 := by
    simpa only [r, s] using hroot6
  have hrootStar' :
    gaussianMRStarD * R = gaussianMRStarConductor * L + gaussianMRStarBeta * S + 29 := by
    simpa only [R, S] using hrootStar
  have hnewEq :
    gaussianMR6FifthsD * r - gaussianMR6FifthsBeta * s = gaussianMR6FifthsConductor * L + 29 := by
    nlinarith only [hroot6']
  have hstarEq :
    gaussianMRStarD * R - gaussianMRStarBeta * S = gaussianMRStarConductor * L + 29 := by
    nlinarith only [hrootStar']
  have hconductors : gaussianMR6FifthsConductor = gaussianMRStarConductor := by
    norm_num only [gaussianMR6FifthsConductor, gaussianMRStarConductor]
  have hrad : r < q * R := by
    by_contra hnot
    have hbad : q * R ≤ r := le_of_not_gt hnot
    let t : ℝ := Real.sqrt q * S
    have htpos : 0 < t := by
      dsimp only [t]
      exact mul_pos (Real.sqrt_pos.2 (by norm_num only [q])) hSpos
    have htSq : t ^ 2 = q * R := by
      dsimp only [t]
      rw [mul_pow, hqrootSq, hR]
    have hsle : t ≤ s := by
      by_contra hsnot
      have hdiff : 0 < t - s := by linarith only [hsnot]
      have hsum : 0 < t + s := by positivity
      have hsquare : s ^ 2 < t ^ 2 := by nlinarith only [hdiff, hsum]
      nlinarith only [hsquare, htSq, hbad, hr]
    have hsumLower : 34 ≤ s + t := by
      have htlower : 17 ≤ t := by
        dsimp only [t]
        have hrootLower : 1 ≤ Real.sqrt q := by
          have hqrootSq' := hqrootSq
          norm_num only [q] at hqrootSq' ⊢
          nlinarith only [hqrootSq', Real.sqrt_nonneg q]
        nlinarith only [hrootLower, hSlo]
      linarith only [hsle, htlower]
    have hmonoCoef : gaussianMR6FifthsD * (s + t) ≥ gaussianMR6FifthsBeta := by
      have hDscaled := mul_le_mul_of_nonneg_left hsumLower hD6.le
      norm_num [gaussianMR6FifthsD, gaussianMR6FifthsIndex, gaussianMR6FifthsMass,
        gaussianMR6FifthsEndpoint, gaussianMR6FifthsBeta, gaussianMR6FifthsIndex,
        gaussianMR6FifthsMass] at hDscaled ⊢
      nlinarith only [hDscaled]
    have hfactor : r - t ^ 2 = (s - t) * (s + t) := by
      rw [← hr]
      ring_nf
    have hmono :
      gaussianMR6FifthsD * t ^ 2 - gaussianMR6FifthsBeta * t ≤
        gaussianMR6FifthsD * r - gaussianMR6FifthsBeta * s := by
      have hnonneg := mul_nonneg (sub_nonneg.mpr hsle) (sub_nonneg.mpr hmonoCoef)
      have hidentity :
        gaussianMR6FifthsD * r - gaussianMR6FifthsBeta * s -
            (gaussianMR6FifthsD * t ^ 2 - gaussianMR6FifthsBeta * t) =
          (s - t) * (gaussianMR6FifthsD * (s + t) - gaussianMR6FifthsBeta) := by
        rw [← hr]
        ring_nf
      nlinarith only [hnonneg, hidentity]
    have hsqrtBound : t ≤ (113 / 100 : ℝ) * S := by
      dsimp only [t]
      exact mul_le_mul_of_nonneg_right hqroot hSpos.le
    have hbetaScaled := mul_le_mul_of_nonneg_left hsqrtBound hBeta6.le
    have hbetaScaled' : gaussianMR6FifthsBeta * t ≤ gaussianMR6FifthsBeta * (113 / 100) * S := by
      calc
        gaussianMR6FifthsBeta * t ≤ gaussianMR6FifthsBeta * (113 / 100 * S) := hbetaScaled
        _ = gaussianMR6FifthsBeta * (113 / 100) * S := by ring
    have hnewStrict :
      gaussianMR6FifthsD * t ^ 2 - gaussianMR6FifthsBeta * t >
        gaussianMRStarD * R - gaussianMRStarBeta * S := by
      have hrewrite :
        gaussianMR6FifthsD * t ^ 2 - gaussianMR6FifthsBeta * t =
          gaussianMR6FifthsD * q * R - gaussianMR6FifthsBeta * t := by
        rw [htSq]
        ring
      have hstep :
        gaussianMR6FifthsD * q * R - gaussianMR6FifthsBeta * (113 / 100) * S ≤
          gaussianMR6FifthsD * q * R - gaussianMR6FifthsBeta * t := by
        nlinarith only [hbetaScaled']
      calc
        gaussianMR6FifthsD * t ^ 2 - gaussianMR6FifthsBeta * t =
            gaussianMR6FifthsD * q * R - gaussianMR6FifthsBeta * t :=
          hrewrite
        _ ≥ gaussianMR6FifthsD * q * R - gaussianMR6FifthsBeta * (113 / 100) * S := hstep
        _ > gaussianMRStarD * R - gaussianMRStarBeta * S := hscalar
    have hnew := hnewStrict.trans_le hmono
    have hbudgetEq :
      gaussianMR6FifthsD * r - gaussianMR6FifthsBeta * s =
        gaussianMRStarD * R - gaussianMRStarBeta * S := by
      rw [hnewEq, hstarEq, hconductors]
    rw [hbudgetEq] at hnew
    exact (lt_irrefl (gaussianMRStarD * R - gaussianMRStarBeta * S)) hnew
  have hrnonneg : 0 ≤ r := by
    dsimp only [r]
    exact sq_nonneg (gaussianMR6FifthsRoot L)
  have hRnonneg : 0 ≤ R := by
    dsimp only [R]
    exact sq_nonneg (gaussianMRStarRoot L)
  have hboundSq : r ^ 2 < (q * R) ^ 2 := by
    have hscaled := mul_lt_mul_of_pos_right hrad (by positivity : 0 < r + q * R)
    nlinarith only [hscaled, hrad, hrnonneg, hRnonneg, hqpos]
  have hcoeffEq : (6 / 5 : ℝ) * q ^ 2 = (2601 / 2800 : ℝ) * (21 / 10) := by norm_num [q]
  dsimp only [gaussianMR6FifthsBound, gaussianMRStarBound]
  calc
    (6 / 5 : ℝ) * gaussianMR6FifthsRadius L ^ 2 < (6 / 5 : ℝ) * (q * gaussianMRStarRadius L) ^ 2 :=
      by exact mul_lt_mul_of_pos_left hboundSq (by norm_num only)
    _ = (6 / 5 : ℝ) * q ^ 2 * gaussianMRStarRadius L ^ 2 := by ring
    _ = (2601 / 2800 : ℝ) * (21 / 10) * gaussianMRStarRadius L ^ 2 := by rw [hcoeffEq]
    _ = (2601 / 2800 : ℝ) * (21 / 10 * gaussianMRStarRadius L ^ 2) := by ring

/-- The 6/5 budget radius is below `19/25` of the logarithmic scale for
`L >= 500`. The proof evaluates its defining quadratic at that radius. -/
theorem gaussianMR6FifthsRadius_upper_19_25 {L : ℝ} (hL : 500 ≤ L) :
    gaussianMR6FifthsRadius L < (19 / 25 : ℝ) * L := by
  let u : ℝ := Real.sqrt ((19 / 25 : ℝ) * L)
  have hLpos : 0 < L := by linarith only [hL]
  have hD : (639999 / 1000000 : ℝ) ≤ gaussianMR6FifthsD := by
    norm_num [gaussianMR6FifthsD, gaussianMR6FifthsIndex, gaussianMR6FifthsMass,
      gaussianMR6FifthsEndpoint]
  have hBeta : gaussianMR6FifthsBeta ≤ (257 / 500 : ℝ) := by
    norm_num [gaussianMR6FifthsBeta, gaussianMR6FifthsIndex, gaussianMR6FifthsMass]
  have hDpos := gaussianMR6Fifths_coefficients_pos.1
  have hBetaPos := gaussianMR6Fifths_coefficients_pos.2
  have huSq : u ^ 2 = (19 / 25 : ℝ) * L := by
    dsimp only [u]
    rw [Real.sq_sqrt]
    positivity
  have huPos : 0 < u := by
    dsimp only [u]
    exact Real.sqrt_pos.2 (by positivity)
  have huLe : u ≤ L / 25 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith only [hL]
  have hbudget := gaussianMR6FifthsRadius_equation hL
  have hroot := gaussianMR6FifthsRoot_pos hL
  have hrootEq :
    gaussianMR6FifthsD * gaussianMR6FifthsRoot L ^ 2 =
      gaussianMR6FifthsConductor * L + gaussianMR6FifthsBeta * gaussianMR6FifthsRoot L + 29 := by
    simpa only [gaussianMR6FifthsRadius] using hbudget
  have hmarginSlope :
    (63 / 1000 : ℝ) < (639999 / 1000000 : ℝ) * (19 / 25) - (161 / 400 : ℝ) - (257 / 500) / 25 := by
    norm_num only
  have hmargin :
    0 <
      gaussianMR6FifthsD * u ^ 2 - gaussianMR6FifthsBeta * u -
        (gaussianMR6FifthsConductor * L + 29) := by
    have hDscaled := mul_le_mul_of_nonneg_right hD (sq_nonneg u)
    have hbetascaled := mul_le_mul hBeta huLe huPos.le (by norm_num only : (0 : ℝ) ≤ 257 / 500)
    have hmarginL := mul_lt_mul_of_pos_right hmarginSlope hLpos
    have hconstant : 29 < (63 / 1000 : ℝ) * L := by nlinarith only [hL]
    rw [huSq] at hDscaled
    norm_num only [gaussianMR6FifthsConductor] at hmarginL ⊢
    rw [huSq]
    nlinarith only [hDscaled, hbetascaled, hmarginL, hconstant]
  have hu19 : 19 ≤ u := by
    dsimp only [u]
    exact (Real.le_sqrt (by norm_num only) (by positivity)).2 (by nlinarith only [hL])
  have hsum : 19 ≤ u + gaussianMR6FifthsRoot L := by linarith only [hu19, hroot]
  have hcoef : 0 < gaussianMR6FifthsD * (u + gaussianMR6FifthsRoot L) - gaussianMR6FifthsBeta := by
    have hmul := mul_le_mul hD hsum (by norm_num only : (0 : ℝ) ≤ 19) hDpos.le
    nlinarith only [hmul, hBeta]
  have hrad : gaussianMR6FifthsRoot L < u := by
    by_contra hnot
    have hbad : u ≤ gaussianMR6FifthsRoot L := le_of_not_gt hnot
    have hidentity :
      gaussianMR6FifthsD * u ^ 2 - gaussianMR6FifthsBeta * u -
          (gaussianMR6FifthsConductor * L + 29) -
          (gaussianMR6FifthsD * gaussianMR6FifthsRoot L ^ 2 -
            gaussianMR6FifthsBeta * gaussianMR6FifthsRoot L -
            (gaussianMR6FifthsConductor * L + 29)) =
        (u - gaussianMR6FifthsRoot L) *
          (gaussianMR6FifthsD * (u + gaussianMR6FifthsRoot L) - gaussianMR6FifthsBeta) := by
      ring
    have hprod :
      (u - gaussianMR6FifthsRoot L) *
          (gaussianMR6FifthsD * (u + gaussianMR6FifthsRoot L) - gaussianMR6FifthsBeta) ≤
        0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith only [hbad]) hcoef.le
    nlinarith only [hmargin, hrootEq, hidentity, hprod]
  have hsquare : gaussianMR6FifthsRoot L ^ 2 < u ^ 2 :=
    (sq_lt_sq₀ (le_of_lt hroot) (le_of_lt huPos)).2 hrad
  dsimp only [gaussianMR6FifthsRadius]
  nlinarith only [hsquare, huSq]

/-- The 6/5 Gaussian bound is below `7/10 * L^2` from `L = 500` onward. -/
theorem gaussianMR6FifthsBound_lt_sevenTenths_sq {L : ℝ} (hL : 500 ≤ L) :
    gaussianMR6FifthsBound L < (7 / 10 : ℝ) * L ^ 2 := by
  have hrad := gaussianMR6FifthsRadius_upper_19_25 hL
  have hLpos : 0 < L := by linarith only [hL]
  have hL0 : 0 ≤ L := le_of_lt hLpos
  have hr0 : 0 ≤ gaussianMR6FifthsRadius L := by
    dsimp only [gaussianMR6FifthsRadius]
    positivity
  have hc0 : 0 ≤ (19 / 25 : ℝ) := by norm_num only
  have hsq : gaussianMR6FifthsRadius L ^ 2 ≤ ((19 / 25 : ℝ) * L) ^ 2 := by
    nlinarith only [hrad, hr0, mul_nonneg hc0 hL0]
  have hratio : (6 / 5 : ℝ) * (19 / 25) ^ 2 < 7 / 10 := by norm_num only
  have hscaled := mul_le_mul_of_nonneg_left hsq (by norm_num only : (0 : ℝ) ≤ 6 / 5)
  dsimp only [gaussianMR6FifthsBound]
  have hratioL := mul_lt_mul_of_pos_right hratio (sq_pos_of_pos hLpos)
  ring_nf at hratioL ⊢
  nlinarith only [hscaled, hratioL]

/-- The constant-6 radius satisfies its quadratic budget equation. -/
theorem gaussianMR6Radius_equation {L : ℝ} (hL : 300 ≤ L) :
    gaussianMR6FifthsD * gaussianMR6Radius L =
      gaussianMR6FifthsConductor * L + gaussianMR6FifthsBeta * gaussianMR6Root L + 6 := by
  let z :=
    Real.sqrt
      (gaussianMR6FifthsBeta ^ 2 + 4 * gaussianMR6FifthsD * (gaussianMR6FifthsConductor * L + 6))
  have hD : 0 < gaussianMR6FifthsD := by
    norm_num only [gaussianMR6FifthsD, gaussianMR6FifthsIndex, gaussianMR6FifthsMass,
      gaussianMR6FifthsEndpoint]
  have hB : 0 < gaussianMR6FifthsBeta := by
    norm_num only [gaussianMR6FifthsBeta, gaussianMR6FifthsIndex, gaussianMR6FifthsMass]
  have hC : 0 < gaussianMR6FifthsConductor := by norm_num only [gaussianMR6FifthsConductor]
  have harg :
    0 ≤
      gaussianMR6FifthsBeta ^ 2 +
        4 * gaussianMR6FifthsD * (gaussianMR6FifthsConductor * L + 6) := by
    have hL' : 0 ≤ L := by linarith only [hL]
    have hterm : 0 ≤ gaussianMR6FifthsConductor * L + 6 := by positivity
    positivity
  have hz :
    z ^ 2 =
      gaussianMR6FifthsBeta ^ 2 +
        4 * gaussianMR6FifthsD * (gaussianMR6FifthsConductor * L + 6) := by
    dsimp only [z]
    rw [Real.sq_sqrt harg]
  have hD0 : gaussianMR6FifthsD ≠ 0 := ne_of_gt hD
  have hlin : 2 * gaussianMR6FifthsD * gaussianMR6Root L = gaussianMR6FifthsBeta + z := by
    dsimp only [gaussianMR6Root, z]
    field_simp [hD0]
  calc
    gaussianMR6FifthsD * gaussianMR6Radius L =
        (4 * gaussianMR6FifthsD ^ 2 * gaussianMR6Root L ^ 2) / (4 * gaussianMR6FifthsD) :=
      by
      dsimp only [gaussianMR6Radius]
      field_simp [hD0]
    _ = (gaussianMR6FifthsBeta + z) ^ 2 / (4 * gaussianMR6FifthsD) := by
      rw [← hlin]
      ring_nf
    _ =
        (gaussianMR6FifthsBeta ^ 2 + 2 * gaussianMR6FifthsBeta * z + z ^ 2) /
          (4 * gaussianMR6FifthsD) :=
      by ring_nf
    _ =
        (2 * gaussianMR6FifthsBeta ^ 2 + 2 * gaussianMR6FifthsBeta * z +
            4 * gaussianMR6FifthsD * (gaussianMR6FifthsConductor * L + 6)) /
          (4 * gaussianMR6FifthsD) :=
      by
      rw [hz]; ring_nf
    _ =
        (2 * gaussianMR6FifthsBeta * (gaussianMR6FifthsBeta + z) +
            4 * gaussianMR6FifthsD * (gaussianMR6FifthsConductor * L + 6)) /
          (4 * gaussianMR6FifthsD) :=
      by ring_nf
    _ =
        (2 * gaussianMR6FifthsBeta * (2 * gaussianMR6FifthsD * gaussianMR6Root L) +
            4 * gaussianMR6FifthsD * (gaussianMR6FifthsConductor * L + 6)) /
          (4 * gaussianMR6FifthsD) :=
      by rw [hlin]
    _ = gaussianMR6FifthsConductor * L + gaussianMR6FifthsBeta * gaussianMR6Root L + 6 := by
      field_simp [hD0]
      ring_nf

/-- The constant-6 root is positive throughout its range. -/
theorem gaussianMR6Root_pos {L : ℝ} (hL : 300 ≤ L) : 0 < gaussianMR6Root L := by
  have hD : 0 < gaussianMR6FifthsD := gaussianMR6Fifths_coefficients_pos.1
  have hB : 0 < gaussianMR6FifthsBeta := gaussianMR6Fifths_coefficients_pos.2
  have hC : 0 < gaussianMR6FifthsConductor := by norm_num only [gaussianMR6FifthsConductor]
  have hL' : 0 ≤ L := by linarith only [hL]
  have hterm : 0 < gaussianMR6FifthsConductor * L + 6 := by positivity
  have harg :
    0 <
      gaussianMR6FifthsBeta ^ 2 +
        4 * gaussianMR6FifthsD * (gaussianMR6FifthsConductor * L + 6) := by
    positivity
  have hnum :
    0 <
      gaussianMR6FifthsBeta +
        Real.sqrt
          (gaussianMR6FifthsBeta ^ 2 +
            4 * gaussianMR6FifthsD * (gaussianMR6FifthsConductor * L + 6)) :=
    add_pos_of_pos_of_nonneg hB (Real.sqrt_nonneg _)
  have hden : 0 < 2 * gaussianMR6FifthsD := by positivity
  dsimp only [gaussianMR6Root]
  exact div_pos hnum hden

/-- The constant-6 root is at least 14 from logarithmic scale 300 onward. -/
theorem gaussianMR6Root_lower_14 {L : ℝ} (hL : 300 ≤ L) : 14 ≤ gaussianMR6Root L := by
  by_contra hnot
  have hlt : gaussianMR6Root L < 14 := lt_of_not_ge hnot
  have hEq := gaussianMR6Radius_equation hL
  have heq :
    gaussianMR6FifthsD * gaussianMR6Root L ^ 2 - gaussianMR6FifthsBeta * gaussianMR6Root L =
      gaussianMR6FifthsConductor * L + 6 := by
    dsimp only [gaussianMR6Radius] at hEq
    nlinarith only [hEq]
  have hmono : 0 < gaussianMR6FifthsD * (14 + gaussianMR6Root L) - gaussianMR6FifthsBeta := by
    have hbase : 0 < gaussianMR6FifthsD * 14 - gaussianMR6FifthsBeta := by
      norm_num only [gaussianMR6FifthsD, gaussianMR6FifthsIndex, gaussianMR6FifthsMass,
        gaussianMR6FifthsEndpoint, gaussianMR6FifthsBeta]
    nlinarith only [hbase, gaussianMR6Fifths_coefficients_pos.1, gaussianMR6Root_pos hL]
  have hfactor := mul_nonneg (sub_nonneg.mpr hlt.le) hmono.le
  have hpoly :
    gaussianMR6FifthsD * gaussianMR6Root L ^ 2 - gaussianMR6FifthsBeta * gaussianMR6Root L ≤
      gaussianMR6FifthsD * 196 - 14 * gaussianMR6FifthsBeta := by
    nlinarith only [hfactor]
  have hanchor :
    gaussianMR6FifthsD * 196 - 14 * gaussianMR6FifthsBeta - 300 * gaussianMR6FifthsConductor - 6 <
      0 := by
    norm_num only [gaussianMR6FifthsD, gaussianMR6FifthsIndex, gaussianMR6FifthsMass,
      gaussianMR6FifthsEndpoint, gaussianMR6FifthsBeta, gaussianMR6FifthsConductor]
  have hC : 0 < gaussianMR6FifthsConductor := by norm_num only [gaussianMR6FifthsConductor]
  have hlower :
    300 * gaussianMR6FifthsConductor + 6 ≤
      gaussianMR6FifthsD * gaussianMR6Root L ^ 2 - gaussianMR6FifthsBeta * gaussianMR6Root L := by
    rw [heq]
    nlinarith only [hL, hC]
  linarith only [hpoly, hanchor, hlower]

/-- The constant-6 root and witness bound are dominated by the corresponding
constant-18 quantities. -/
theorem gaussianMR6Bound_le_gaussianMR18Bound {L : ℝ} (hL : 300 ≤ L) :
    gaussianMR6Bound L ≤ gaussianMR18Bound L := by
  have hD : 0 < gaussianMR6FifthsD := gaussianMR6Fifths_coefficients_pos.1
  have hB : 0 < gaussianMR6FifthsBeta := gaussianMR6Fifths_coefficients_pos.2
  have hC : 0 < gaussianMR6FifthsConductor := by norm_num only [gaussianMR6FifthsConductor]
  have harg :
    gaussianMR6FifthsBeta ^ 2 + 4 * gaussianMR6FifthsD * (gaussianMR6FifthsConductor * L + 6) ≤
      gaussianMR6FifthsBeta ^ 2 +
        4 * gaussianMR6FifthsD * (gaussianMR6FifthsConductor * L + 18) := by
    have hstep : 0 ≤ 4 * gaussianMR6FifthsD * 12 := by positivity
    nlinarith only [hstep]
  have hroot : gaussianMR6Root L ≤ gaussianMR18Root L := by
    dsimp only [gaussianMR6Root, gaussianMR18Root]
    exact
      div_le_div_of_nonneg_right (add_le_add_right (Real.sqrt_le_sqrt harg) gaussianMR6FifthsBeta)
        (by positivity)
  have hrootpos : 0 ≤ gaussianMR6Root L := (gaussianMR6Root_pos hL).le
  have hroot18pos : 0 ≤ gaussianMR18Root L := (gaussianMR18Root_pos hL).le
  have hsqmul := mul_self_le_mul_self hrootpos hroot
  have hsq : gaussianMR6Root L ^ 2 ≤ gaussianMR18Root L ^ 2 := by simpa only [pow_two] using hsqmul
  have hfourthmul := mul_self_le_mul_self (sq_nonneg (gaussianMR6Root L)) hsq
  have hfourth : (gaussianMR6Root L ^ 2) ^ 2 ≤ (gaussianMR18Root L ^ 2) ^ 2 := by
    simpa only [pow_two] using hfourthmul
  dsimp only [gaussianMR6Bound, gaussianMR6Radius, gaussianMR18Bound, gaussianMR18Radius]
  exact mul_le_mul_of_nonneg_left hfourth (by norm_num only)

/-- The constant-6 witness bound is strictly below the constant-18 bound. -/
theorem gaussianMR6Bound_lt_gaussianMR18Bound {L : ℝ} (hL : 300 ≤ L) :
    gaussianMR6Bound L < gaussianMR18Bound L := by
  have hD : 0 < gaussianMR6FifthsD := gaussianMR6Fifths_coefficients_pos.1
  have hC : 0 < gaussianMR6FifthsConductor := by norm_num only [gaussianMR6FifthsConductor]
  have harg :
    gaussianMR6FifthsBeta ^ 2 + 4 * gaussianMR6FifthsD * (gaussianMR6FifthsConductor * L + 6) <
      gaussianMR6FifthsBeta ^ 2 +
        4 * gaussianMR6FifthsD * (gaussianMR6FifthsConductor * L + 18) := by
    have hstep : 0 < 4 * gaussianMR6FifthsD * 12 := by positivity
    nlinarith only [hstep]
  have hLpos : 0 < L := by linarith only [hL]
  have hargpos :
    0 ≤
      gaussianMR6FifthsBeta ^ 2 +
        4 * gaussianMR6FifthsD * (gaussianMR6FifthsConductor * L + 6) := by
    positivity
  have hroot : gaussianMR6Root L < gaussianMR18Root L := by
    dsimp only [gaussianMR6Root, gaussianMR18Root]
    exact
      div_lt_div_of_pos_right
        (add_lt_add_right (Real.sqrt_lt_sqrt hargpos harg) gaussianMR6FifthsBeta) (by positivity)
  have hrootpos : 0 ≤ gaussianMR6Root L := (gaussianMR6Root_pos hL).le
  have hroot18pos : 0 ≤ gaussianMR18Root L := (gaussianMR18Root_pos hL).le
  have hsq : gaussianMR6Root L ^ 2 < gaussianMR18Root L ^ 2 :=
    (sq_lt_sq₀ hrootpos hroot18pos).2 hroot
  have hfourth : (gaussianMR6Root L ^ 2) ^ 2 < (gaussianMR18Root L ^ 2) ^ 2 :=
    (sq_lt_sq₀ (sq_nonneg (gaussianMR6Root L)) (sq_nonneg (gaussianMR18Root L))).2 hsq
  have hscaled := mul_lt_mul_of_pos_left hfourth (by norm_num only : (0 : ℝ) < 6 / 5)
  dsimp only [gaussianMR6Bound, gaussianMR6Radius, gaussianMR18Bound, gaussianMR18Radius]
  exact hscaled

/-- The constant-6 squared radius dominates the affine scale needed by the
signed prefix comparison. -/
theorem gaussianMR6Radius_lower {L : ℝ} (hL : 300 ≤ L) :
    (5 / 8 : ℝ) * L + 20 ≤ gaussianMR6Radius L := by
  by_contra hnot
  have hlt : gaussianMR6Radius L < (5 / 8 : ℝ) * L + 20 := lt_of_not_ge hnot
  dsimp only [gaussianMR6Radius] at hlt
  have hEq := gaussianMR6Radius_equation hL
  have hs := gaussianMR6Root_lower_14 hL
  have hD : 0 < gaussianMR6FifthsD := gaussianMR6Fifths_coefficients_pos.1
  have hB : 0 < gaussianMR6FifthsBeta := gaussianMR6Fifths_coefficients_pos.2
  have hC : 0 < gaussianMR6FifthsConductor := by norm_num only [gaussianMR6FifthsConductor]
  have hcoef : 0 < gaussianMR6FifthsConductor - (5 / 8 : ℝ) * gaussianMR6FifthsD := by
    norm_num only [gaussianMR6FifthsConductor, gaussianMR6FifthsD, gaussianMR6FifthsIndex,
      gaussianMR6FifthsMass, gaussianMR6FifthsEndpoint]
  have hanchor :
    0 ≤
      300 * (gaussianMR6FifthsConductor - (5 / 8 : ℝ) * gaussianMR6FifthsD) +
          14 * gaussianMR6FifthsBeta +
          6 -
        20 * gaussianMR6FifthsD := by
    norm_num only [gaussianMR6FifthsConductor, gaussianMR6FifthsD, gaussianMR6FifthsIndex,
      gaussianMR6FifthsMass, gaussianMR6FifthsEndpoint, gaussianMR6FifthsBeta]
  have hL300 : 0 ≤ L - 300 := by linarith only [hL]
  have hstep := mul_nonneg hL300 hcoef.le
  have hbeta := mul_le_mul_of_nonneg_left hs hB.le
  have hscaled := mul_lt_mul_of_pos_left hlt hD
  dsimp only [gaussianMR6Radius] at hEq ⊢
  nlinarith only [hEq, hstep, hbeta, hanchor, hscaled]

/-- The constant-6 witness bound reaches the finite 50000-prime prefix. -/
theorem gaussianMR6Bound_gt_prefix {L : ℝ} (hL : 300 ≤ L) : 50000 < gaussianMR6Bound L := by
  have hr := gaussianMR6Radius_lower hL
  have hbase : (415 / 2 : ℝ) ≤ gaussianMR6Radius L := by
    dsimp only [gaussianMR6Radius] at hr ⊢
    nlinarith only [hL, hr]
  have hsq : (415 / 2 : ℝ) ^ 2 ≤ gaussianMR6Radius L ^ 2 := by
    have hnonneg : 0 ≤ (415 / 2 : ℝ) := by norm_num only
    have hmul := mul_self_le_mul_self hnonneg hbase
    nlinarith only [hmul]
  have hscaled := mul_le_mul_of_nonneg_left hsq (by norm_num only : (0 : ℝ) ≤ 6 / 5)
  have hstrict : 50000 < (6 / 5 : ℝ) * (415 / 2) ^ 2 := by norm_num only
  dsimp only [gaussianMR6Bound]
  linarith only [hstrict, hscaled]

/-- The constant-6 bound strictly exceeds `3/10 * L^2` from scale 300. -/
theorem gaussianMR6Bound_gt_local_three_tenths {L : ℝ} (hL : 300 ≤ L) :
    (3 / 10 : ℝ) * L ^ 2 < gaussianMR6Bound L := by
  have hr := gaussianMR6Radius_lower hL
  have hLpos : 0 < L := by linarith only [hL]
  have hbase : (5 / 8 : ℝ) * L < gaussianMR6Radius L := by linarith only [hr]
  have hrad : ((5 / 8 : ℝ) * L) ^ 2 < gaussianMR6Radius L ^ 2 :=
    (sq_lt_sq₀ (mul_nonneg (by norm_num only) hLpos.le)
          (le_trans (mul_nonneg (by norm_num only) hLpos.le) hbase.le)).2
      hbase
  have hscaled := mul_lt_mul_of_pos_left hrad (by norm_num only : (0 : ℝ) < 6 / 5)
  have hcoeff : (3 / 10 : ℝ) < (6 / 5) * (5 / 8) ^ 2 := by norm_num only
  have hcoeffL := mul_lt_mul_of_pos_right hcoeff (sq_pos_of_pos hLpos)
  dsimp only [gaussianMR6Bound] at hscaled ⊢
  nlinarith only [hscaled, hcoeffL]

/-- The signed 50000-prefix ambient error fits the constant-6 scalar budget. -/
theorem gaussianMR6_ambient_error_prefix_signed_le {q : ℕ} {L : ℝ} (hL : 300 ≤ L)
    (hq : Real.log q ≤ L) :
    LLS.PaperStatements.gaussianAmbientErrorPrefixSigned q (gaussianMR6Radius L ^ 2) ≤ 27 / 5 := by
  let r := gaussianMR6Radius L
  have hr := gaussianMR6Radius_lower hL
  have hrR : (5 / 8 : ℝ) * L + 20 ≤ r := by simpa only [r] using hr
  have hrad : 415 / 2 ≤ r := by
    have := gaussianMR6Radius_lower hL
    dsimp only [r] at hrR ⊢
    nlinarith only [hrR, hL]
  have hLpos : 0 < L := by linarith only [hL]
  have hrpos : 0 < r := by linarith only [hrad]
  have hsqrt : Real.sqrt (r ^ 2) = r := Real.sqrt_sq hrpos.le
  have hx : (19 / 10 : ℝ) ^ 16 ≤ r ^ 2 := by
    norm_num only at hrad ⊢
    nlinarith only [hrad]
  have hdec :=
    LLS.PaperStatements.rpow_neg_nine_sixteenths_le_div_scale_sqrt (a := 19 / 10) (by norm_num only)
      hx
  have hP : (2129 / 2000 : ℝ) * (((7 / 6) * Real.log q + 4) / r) ≤ 2 := by
    rw [div_eq_mul_inv]
    field_simp [hrpos.ne']
    have hlog := Real.log_natCast_nonneg q
    nlinarith only [hL, hq, hrR, hLpos, hlog]
  have hleft : (473 / 10 : ℝ) * (r ^ 2) ^ (-9 / 16 : ℝ) ≤ 3 / 25 := by
    rw [hsqrt] at hdec
    have hmul := mul_le_mul_of_nonneg_left hdec (by norm_num only : (0 : ℝ) ≤ 473 / 10)
    calc
      (473 / 10 : ℝ) * (r ^ 2) ^ (-9 / 16 : ℝ) ≤ (473 / 10 : ℝ) / ((19 / 10 : ℝ) * r) := by
        rw [div_eq_mul_inv]
        calc
          (473 / 10 : ℝ) * (r ^ 2) ^ (-9 / 16 : ℝ) ≤ (473 / 10 : ℝ) * (1 / ((19 / 10 : ℝ) * r)) :=
            hmul
          _ = (473 / 10 : ℝ) / ((19 / 10 : ℝ) * r) := by ring
      _ ≤ 3 / 25 := by
        field_simp [hrpos.ne']
        nlinarith only [hrad]
  have harch : (512 / 27 : ℝ) / (r ^ 2) ≤ 1 / 1000 := by
    rw [div_le_iff₀ (sq_pos_of_pos hrpos)]
    norm_num only
    nlinarith only [hrad]
  have htotal : (159169 / 50000 : ℝ) + 1 / 1000 + 2 + 3 / 25 ≤ 27 / 5 := by norm_num only
  have hrEq : gaussianMR6Radius L = r := rfl
  have hsqrt' : Real.sqrt (gaussianMR6Radius L ^ 2) = r := by simpa only [r] using hsqrt
  dsimp only [LLS.PaperStatements.gaussianAmbientErrorPrefixSigned]
  rw [hrEq, hsqrt']
  calc
    _ =
        (159169 / 50000 : ℝ) + (512 / 27 : ℝ) / (r ^ 2) +
          ((2129 / 2000 : ℝ) * (((7 / 6) * Real.log q + 4) / r) +
            (473 / 10 : ℝ) * (r ^ 2) ^ (-9 / 16 : ℝ)) :=
      by ring
    _ ≤ (159169 / 50000 : ℝ) + 1 / 1000 + 2 + 3 / 25 := by nlinarith only [harch, hP, hleft]
    _ ≤ 27 / 5 := htotal

/-- The constant-6 radius equation contradicts the signed relative subgroup
comparison for every Fermat subgroup index at least one billion. -/
theorem gaussianMR6_large_index_comparison_impossible {m s r A L : ℝ}
    (hm : gaussianMR6FifthsIndex ≤ m) (hs : 14 ≤ s) (hr : 415 / 2 ≤ r)
    (hgamma : m / (m - 1) ≤ gaussianMR6FifthsIndex / (gaussianMR6FifthsIndex - 1)) (hA : A ≤ 27 / 5)
    (hroot :
      gaussianMR6FifthsD * r = gaussianMR6FifthsConductor * L + gaussianMR6FifthsBeta * s + 6)
    (hcmp :
      gaussianMR6FifthsD * r ≤
        gaussianMR6FifthsConductor * L + gaussianMR6FifthsBeta * s +
          (m / (m - 1)) *
            (63 * gaussianMR6FifthsEndpoint / (10 * s) +
              1839 * gaussianMR6FifthsEndpoint / (1000 * r)) +
          13 / (m - 1) +
          A) :
    False := by
  have herr := gaussianMR6_scalar_error_lt hm hs hr hgamma hA
  have htermEq :
    63 * gaussianMR6FifthsEndpoint / (10 * s) + 1839 * gaussianMR6FifthsEndpoint / (1000 * r) =
      (63 * gaussianMR6FifthsEndpoint / 10) / s +
        (1839 * gaussianMR6FifthsEndpoint / 1000) / r := by
    field_simp
  rw [htermEq, hroot] at hcmp
  rw [htermEq] at herr
  have hle :
    6 ≤
      (m / (m - 1)) *
          ((63 * gaussianMR6FifthsEndpoint / 10) / s +
            (1839 * gaussianMR6FifthsEndpoint / 1000) / r) +
        13 / (m - 1) +
        A := by
    nlinarith only [hcmp]
  exact (not_le_of_gt herr) hle

/-- The constant-6 radius contradicts the index-four comparison when the
signed prefix residual is at most eleven. -/
theorem gaussianMR6_triple_comparison_impossible {L : ℝ} (hL : 300 ≤ L)
    (hcmp :
      ((4 * gaussianMR6FifthsMass - gaussianMR6FifthsEndpoint) / 3) * gaussianMR6Radius L ≤
        (161 / 600 : ℝ) * L +
          (4 / 3 : ℝ) * (gaussianMR6FifthsMass / 3 + 3 / 10) * gaussianMR6Root L +
          11) :
    False := by
  let r := gaussianMR6Radius L
  let s := gaussianMR6Root L
  have hrlo : 415 / 2 ≤ r := by
    dsimp only [r]
    have hrad := gaussianMR6Radius_lower hL
    nlinarith only [hrad, hL]
  have hspos : 0 < s := by
    dsimp only [s]
    exact gaussianMR6Root_pos hL
  have hsSq : s ^ 2 = r := by dsimp only [s, r, gaussianMR6Radius]
  have hs14 : 14 ≤ s := by nlinarith only [hsSq, hrlo, hspos]
  have hsle : s ≤ r / 14 := by
    apply (le_div_iff₀ (by norm_num only : (0 : ℝ) < 14)).2
    nlinarith only [hsSq, hs14]
  have hroot := gaussianMR6Radius_equation hL
  have hroot' :
    gaussianMR6FifthsD * r = gaussianMR6FifthsConductor * L + gaussianMR6FifthsBeta * s + 6 := by
    simpa only [r, s] using hroot
  have hindexCmp :
    (((4 * gaussianMR6FifthsMass - gaussianMR6FifthsEndpoint) / 3) -
          (2 / 3 : ℝ) * gaussianMR6FifthsD) *
        r ≤
      ((4 / 3 : ℝ) * (gaussianMR6FifthsMass / 3 + 3 / 10) - (2 / 3 : ℝ) * gaussianMR6FifthsBeta) *
          s +
        7 := by
    change
      ((4 * gaussianMR6FifthsMass - gaussianMR6FifthsEndpoint) / 3) * r ≤
        (161 / 600 : ℝ) * L + (4 / 3 : ℝ) * (gaussianMR6FifthsMass / 3 + 3 / 10) * s + 11 at hcmp
    have hc : gaussianMR6FifthsConductor = 161 / 400 := by
      norm_num only [gaussianMR6FifthsConductor]
    rw [hc] at hroot'
    nlinarith only [hcmp, hroot']
  have hbetaDiff :
    0 <
      (4 / 3 : ℝ) * (gaussianMR6FifthsMass / 3 + 3 / 10) - (2 / 3 : ℝ) * gaussianMR6FifthsBeta := by
    norm_num [gaussianMR6FifthsBeta, gaussianMR6FifthsIndex, gaussianMR6FifthsMass]
  have hgap :
    (((4 * gaussianMR6FifthsMass - gaussianMR6FifthsEndpoint) / 3) -
          (2 / 3 : ℝ) * gaussianMR6FifthsD) -
        ((4 / 3 : ℝ) * (gaussianMR6FifthsMass / 3 + 3 / 10) - (2 / 3 : ℝ) * gaussianMR6FifthsBeta) /
          14 >
      0 := by
    norm_num [gaussianMR6FifthsD, gaussianMR6FifthsBeta, gaussianMR6FifthsIndex,
      gaussianMR6FifthsMass, gaussianMR6FifthsEndpoint, gaussianMR6FifthsConductor]
  have hmargin :
    (7 : ℝ) <
      (((4 * gaussianMR6FifthsMass - gaussianMR6FifthsEndpoint) / 3) -
            (2 / 3 : ℝ) * gaussianMR6FifthsD) *
          (415 / 2) -
        ((4 / 3 : ℝ) * (gaussianMR6FifthsMass / 3 + 3 / 10) - (2 / 3 : ℝ) * gaussianMR6FifthsBeta) *
          (415 / 28) := by
    norm_num [gaussianMR6FifthsD, gaussianMR6FifthsBeta, gaussianMR6FifthsIndex,
      gaussianMR6FifthsMass, gaussianMR6FifthsEndpoint, gaussianMR6FifthsConductor]
  have hstrict :
    (7 : ℝ) <
      (((4 * gaussianMR6FifthsMass - gaussianMR6FifthsEndpoint) / 3) -
            (2 / 3 : ℝ) * gaussianMR6FifthsD) *
          r -
        ((4 / 3 : ℝ) * (gaussianMR6FifthsMass / 3 + 3 / 10) - (2 / 3 : ℝ) * gaussianMR6FifthsBeta) *
          s := by
    have hscaled := mul_le_mul_of_nonneg_left hsle hbetaDiff.le
    have hlow := mul_le_mul_of_nonneg_left hrlo (le_of_lt hgap)
    nlinarith only [hscaled, hlow, hmargin]
  apply (not_le_of_gt hstrict)
  nlinarith only [hindexCmp]

/-- The constant-6 radius is strictly below `0.71 L` from scale 300. -/
theorem gaussianMR6Radius_lt_71_over_100_scale {L : ℝ} (hL : 300 ≤ L) :
    gaussianMR6Radius L < (71 / 100 : ℝ) * L := by
  let R0 := (71 / 100 : ℝ) * L
  let s := gaussianMR6Root L
  let r := gaussianMR6Radius L
  let A :=
    (639999 / 1000000 : ℝ) * (71 / 100) - gaussianMR6FifthsConductor - (257 / 500 : ℝ) * (1 / 20)
  have hLpos : 0 < L := by linarith only [hL]
  have hspos : 0 < s := gaussianMR6Root_pos hL
  have hsq : r = s ^ 2 := by dsimp only [r, gaussianMR6Radius, s]
  have hs14 := gaussianMR6Root_lower_14 hL
  have hRpos : 0 < R0 := by
    dsimp only [R0]; positivity
  have hLprod : 300 * L ≤ L ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hL (le_of_lt hLpos)
    nlinarith only [hmul]
  have hR0upper : Real.sqrt R0 ≤ (1 / 20 : ℝ) * L := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · dsimp only [R0]
      nlinarith only [hLprod]
  have hD : (639999 / 1000000 : ℝ) ≤ gaussianMR6FifthsD := by
    norm_num only [gaussianMR6FifthsD, gaussianMR6FifthsIndex, gaussianMR6FifthsMass,
      gaussianMR6FifthsEndpoint]
  have hBeta : gaussianMR6FifthsBeta ≤ (257 / 500 : ℝ) := by
    norm_num only [gaussianMR6FifthsBeta, gaussianMR6FifthsIndex, gaussianMR6FifthsMass]
  have hCon : gaussianMR6FifthsConductor = 161 / 400 := by
    norm_num only [gaussianMR6FifthsConductor]
  have hApos : 0 < A := by
    dsimp only [A]
    rw [hCon]
    norm_num only
  have hA300 : 0 < A * 300 - 6 := by
    dsimp only [A]
    rw [hCon]
    norm_num only
  have hlinear : 0 < A * L - 6 := by
    have hstep := mul_nonneg hApos.le (show 0 ≤ L - 300 by linarith only [hL])
    dsimp only [A] at hstep hA300 ⊢
    nlinarith only [hstep, hA300]
  have hmargin :
    0 <
      gaussianMR6FifthsD * R0 - gaussianMR6FifthsConductor * L -
        gaussianMR6FifthsBeta * Real.sqrt R0 -
        6 := by
    have hDscaled := mul_le_mul_of_nonneg_right hD (le_of_lt hRpos)
    have hbetascaled :=
      mul_le_mul hBeta hR0upper (Real.sqrt_nonneg R0) (by norm_num only : (0 : ℝ) ≤ 257 / 500)
    have hbase :
      0 <
        (639999 / 1000000 : ℝ) * (71 / 100) * L - gaussianMR6FifthsConductor * L -
          (257 / 500 : ℝ) * (1 / 20) * L -
          6 := by
      calc
        0 < A * L - 6 := hlinear
        _ =
            (639999 / 1000000 : ℝ) * (71 / 100) * L - gaussianMR6FifthsConductor * L -
              (257 / 500 : ℝ) * (1 / 20) * L -
              6 :=
          by
          dsimp only [A]
          rw [hCon]
          ring
    dsimp only [R0] at hDscaled hbetascaled ⊢
    nlinarith only [hDscaled, hbetascaled, hbase]
  have hEq := gaussianMR6Radius_equation hL
  have hfactorpos : 0 < gaussianMR6FifthsD - gaussianMR6FifthsBeta / (Real.sqrt R0 + s) := by
    have hsum : 14 ≤ Real.sqrt R0 + s := by
      have hsqrt0 : 0 ≤ Real.sqrt R0 := Real.sqrt_nonneg _
      linarith only [hsqrt0, hs14]
    have hmul : (639999 / 1000000 : ℝ) * 14 ≤ gaussianMR6FifthsD * (Real.sqrt R0 + s) := by
      calc
        (639999 / 1000000 : ℝ) * 14 ≤ gaussianMR6FifthsD * 14 := by nlinarith only [hD]
        _ ≤ gaussianMR6FifthsD * (Real.sqrt R0 + s) :=
          mul_le_mul_of_nonneg_left hsum gaussianMR6Fifths_coefficients_pos.1.le
    have hquot : gaussianMR6FifthsBeta / (Real.sqrt R0 + s) < gaussianMR6FifthsD :=
      (div_lt_iff₀ (by linarith only [hsum])).2 (by nlinarith only [hmul, hBeta])
    exact sub_pos.mpr hquot
  have hsumpos : 0 < Real.sqrt R0 + s := add_pos (Real.sqrt_pos.2 hRpos) hspos
  have hsqrtSq : (Real.sqrt R0) ^ 2 = R0 := Real.sq_sqrt hRpos.le
  have hsqrtDiff : Real.sqrt R0 - s = (R0 - s ^ 2) / (Real.sqrt R0 + s) := by
    field_simp [hsumpos.ne']
    nlinarith only [hsqrtSq]
  have hidentity :
    gaussianMR6FifthsD * R0 - gaussianMR6FifthsConductor * L -
        gaussianMR6FifthsBeta * Real.sqrt R0 -
        6 -
        (gaussianMR6FifthsD * r - gaussianMR6FifthsConductor * L - gaussianMR6FifthsBeta * s - 6) =
      (R0 - r) * (gaussianMR6FifthsD - gaussianMR6FifthsBeta / (Real.sqrt R0 + s)) := by
    rw [hsq]
    calc
      _ = gaussianMR6FifthsD * (R0 - s ^ 2) - gaussianMR6FifthsBeta * (Real.sqrt R0 - s) := by ring
      _ = (R0 - s ^ 2) * (gaussianMR6FifthsD - gaussianMR6FifthsBeta / (Real.sqrt R0 + s)) := by
        rw [hsqrtDiff]
        ring
  have hactual :
    gaussianMR6FifthsD * r - gaussianMR6FifthsConductor * L - gaussianMR6FifthsBeta * s - 6 =
      0 := by
    dsimp only [r, s]
    linarith only [hEq]
  have hdiffpos : 0 < R0 - r := by
    by_contra hnot
    have hle : R0 - r ≤ 0 := le_of_not_gt hnot
    have hprod : (R0 - r) * (gaussianMR6FifthsD - gaussianMR6FifthsBeta / (Real.sqrt R0 + s)) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hle hfactorpos.le
    have hId := hidentity
    rw [hactual, sub_zero] at hId
    rw [hId] at hmargin
    exact (not_lt_of_ge hprod) hmargin
  have hout : r < R0 := by linarith only [hdiffpos]
  dsimp only [r, R0] at hout ⊢
  exact hout

/-- The constant-6 Gaussian cutoff is below `0.60492 L²` from scale 300. -/
theorem gaussianMR6Bound_lt_060492_sq {L : ℝ} (hL : 300 ≤ L) :
    gaussianMR6Bound L < (15123 / 25000 : ℝ) * L ^ 2 := by
  have hrad := gaussianMR6Radius_lt_71_over_100_scale hL
  have hLpos : 0 < L := by linarith only [hL]
  have hrpos : 0 < gaussianMR6Radius L := by
    have hlow := gaussianMR6Radius_lower hL
    nlinarith only [hlow, hL]
  have hsq : gaussianMR6Radius L ^ 2 < ((71 / 100 : ℝ) * L) ^ 2 :=
    (sq_lt_sq₀ hrpos.le (mul_nonneg (by norm_num only) hLpos.le)).2 hrad
  have hscaled := mul_lt_mul_of_pos_left hsq (by norm_num only : (0 : ℝ) < 6 / 5)
  have hcoeff : (6 / 5 : ℝ) * (71 / 100) ^ 2 = 15123 / 25000 := by norm_num only
  have hcoeffL : (6 / 5 : ℝ) * ((71 / 100 : ℝ) * L) ^ 2 = (15123 / 25000 : ℝ) * L ^ 2 := by
    calc
      (6 / 5 : ℝ) * ((71 / 100 : ℝ) * L) ^ 2 = ((6 / 5 : ℝ) * (71 / 100) ^ 2) * L ^ 2 := by ring
      _ = (15123 / 25000 : ℝ) * L ^ 2 := by rw [hcoeff]
  dsimp only [gaussianMR6Bound] at hscaled ⊢
  nlinarith only [hscaled, hcoeffL]

end PseudoPrime.Analysis
