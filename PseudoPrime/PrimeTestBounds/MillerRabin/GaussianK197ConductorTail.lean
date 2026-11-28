/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Conductor

/-! # A decreasing majorant for the K197 conductor -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A polynomial majorant for the shifted K197 conductor at nonnegative log displacement. -/
@[expose]
def gaussianConductorPoly197 (z : ℝ) : ℝ :=
  56279 + 19054 * z + 870 * z ^ 2 + 1.41 * z ^ 5

private theorem joint_le_conductor_poly {z : ℝ} (hz : 0 ≤ z) :
    gaussianJoint197 (23 / 2 + z) ≤ gaussianConductorPoly197 z := by
  have he : (23 / 2 : ℝ) + z - 23 / 2 = z := by ring
  have h := joint_poly_upper_197 (show (23 / 2 : ℝ) ≤ 23 / 2 + z by linarith only [hz])
  rw [he] at h
  have hp (j : ℕ) : 0 ≤ z ^ j := pow_nonneg hz j
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ, Nat.reduceAdd,
    add_zero, jointCoeffUpper197, Matrix.cons_val_zero, Matrix.cons_val_succ, Rat.cast_ofScientific,
    Rat.cast_neg] at h
  unfold gaussianConductorPoly197
  linarith only [h, hz, hp 2, hp 3, hp 4, hp 5]

private theorem conductor_slope {z : ℝ} (hz : 0 ≤ z) :
    19054 + 1740 * z + 7.05 * z ^ 4 - (3 / 5) * gaussianConductorPoly197 z ≤ 0 := by
  unfold gaussianConductorPoly197
  by_cases h : z ≤ 25 / 3
  · have h₂ := pow_le_pow_left₀ hz h 2
    have hh := mul_le_mul_of_nonneg_right h₂ (sq_nonneg z)
    nlinarith only [hh, hz, sq_nonneg z, pow_nonneg hz 5]
  · have hh := mul_nonneg (sub_nonneg.mpr (le_of_not_ge h)) (pow_nonneg hz 4)
    nlinarith only [hh, hz, sq_nonneg z]

private theorem conductor_deriv (z : ℝ) :
    HasDerivAt (fun t ↦ gaussianConductorPoly197 t * Real.exp (-(3 / 5) * t))
      ((19054 + 1740 * z + 7.05 * z ^ 4 - (3 / 5) * gaussianConductorPoly197 z) *
        Real.exp (-(3 / 5) * z))
      z := by
  have hp :=
    (((hasDerivAt_id z).const_mul (19054 : ℝ)).const_add 56279).add
        (((hasDerivAt_id z).pow 2).const_mul 870) |>.add
      (((hasDerivAt_id z).pow 5).const_mul 1.41)
  have he := ((hasDerivAt_id z).const_mul (-(3 / 5) : ℝ)).exp
  convert hp.mul he using 1
  · rfl
  · simp only [id, gaussianConductorPoly197, Pi.pow_apply, Pi.add_apply]
    ring

private theorem conductor_major_antitone :
    AntitoneOn (fun z ↦ gaussianConductorPoly197 z * Real.exp (-(3 / 5) * z)) (Set.Ici 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici _)
  · exact fun z _ ↦ (conductor_deriv z).continuousAt.continuousWithinAt
  · exact fun z _ ↦ (conductor_deriv z).differentiableAt.differentiableWithinAt
  · intro z hz
    rw [(conductor_deriv z).deriv]
    exact mul_nonpos_of_nonpos_of_nonneg (conductor_slope (interior_subset hz)) (Real.exp_pos _).le

private theorem rpow_conductor_factor {r : ℝ} (hr : 0 < r) :
    r ^ (-(6 / 5) : ℝ) =
      Real.exp (-(3 / 5) * (23 / 2)) * Real.exp (-(3 / 5) * (2 * Real.log r - 23 / 2)) := by
  rw [← Real.exp_add, Real.rpow_def_of_pos hr]
  congr 1
  ring

/-- A certified left-endpoint majorant bounds the K197 conductor at every
larger radius. The logarithmic half-line starts at displacement zero. -/
theorem gaussian_theta_endpoint_197 {a r C : ℝ} (ha : 0 < a) (har : a ≤ r)
    (hlog : 23 / 2 ≤ 2 * Real.log a)
    (hC :
      (11 / 10) ^ 5 / 30 * a ^ (-(6 / 5) : ℝ) * gaussianConductorPoly197 (2 * Real.log a - 23 / 2) ≤
        C) :
    -C ≤ gaussianTheta197 r := by
  have hl := Real.log_le_log ha har
  have hza := sub_nonneg.mpr hlog
  have hzr : 2 * Real.log a - 23 / 2 ≤ 2 * Real.log r - 23 / 2 := by linarith only [hl]
  have hm := conductor_major_antitone hza (hza.trans hzr) hzr
  have hr := ha.trans_le har
  have hpow :
    r ^ (-(6 / 5) : ℝ) * gaussianConductorPoly197 (2 * Real.log r - 23 / 2) ≤
      a ^ (-(6 / 5) : ℝ) * gaussianConductorPoly197 (2 * Real.log a - 23 / 2) := by
    rw [rpow_conductor_factor hr, rpow_conductor_factor ha]
    linear_combination Real.exp (-(3 / 5) * (23 / 2 : ℝ)) * hm
  have hJ := joint_le_conductor_poly (hza.trans hzr)
  have hJV :
    gaussianJoint197 (2 * Real.log r) ≤ gaussianConductorPoly197 (2 * Real.log r - 23 / 2) := by
    have he : (23 / 2 : ℝ) + (2 * Real.log r - 23 / 2) = 2 * Real.log r := by ring
    rwa [he] at hJ
  have h := (mul_le_mul_of_nonneg_left hJV (Real.rpow_nonneg hr.le _)).trans hpow
  have h' := (mul_le_mul_of_nonneg_left h (by norm_num only : (0 : ℝ) ≤ (11 / 10) ^ 5 / 30))
  unfold gaussianTheta197
  ring_nf at hC h' ⊢
  linarith only [hC, h']

private theorem conductor_poly_mono : MonotoneOn gaussianConductorPoly197 (Set.Ici 0) := by
  intro z hz w _ hzw
  unfold gaussianConductorPoly197
  exact
    add_le_add
      (add_le_add
        (add_le_add_right (mul_le_mul_of_nonneg_left hzw (by norm_num only : (0 : ℝ) ≤ 19054)) _)
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hz hzw 2) (by norm_num only : (0 : ℝ) ≤ 870)))
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hz hzw 5) (by norm_num only : (0 : ℝ) ≤ 1.41))

/-- For every radius at least 334, the K197 conductor contribution is
bounded below by -2.948. Only the endpoint needs numerical certification. -/
theorem gaussian_theta_from334_197 {r : ℝ} (hr : 334 ≤ r) : (-2.948 : ℝ) ≤ gaussianTheta197 r := by
  have hlo :=
    Analysis.rationalLogIntervalCheck_sound (N := 334) (j := 9) (n := 27) (lo := 5.81) (hi :=
      5.81115) (by decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_ofScientific] at hlo
  have hlog : (23 / 2 : ℝ) ≤ 2 * Real.log 334 := by linarith only [hlo.1]
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 334) (p := 6) (d := 5)
        (lo := 0) (hi := 0.000936493) (by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat, neg_div] at hp
  have hP :=
    conductor_poly_mono (sub_nonneg.mpr hlog) (by norm_num only : (0 : ℝ) ≤ 0.1223)
      (show 2 * Real.log 334 - 23 / 2 ≤ 0.1223 by linarith only [hlo.2])
  have hprod :=
    (mul_le_mul_of_nonneg_left hP (Real.rpow_nonneg (by norm_num only) _)).trans
      (mul_le_mul_of_nonneg_right hp (by norm_num only [gaussianConductorPoly197]))
  apply gaussian_theta_endpoint_197 (by norm_num only) hr hlog
  rw [mul_assoc]
  refine
    (mul_le_mul_of_nonneg_left hprod (by norm_num only : (0 : ℝ) ≤ (11 / 10) ^ 5 / 30)).trans ?_
  norm_num only [gaussianConductorPoly197]

/-- On radii from 334 through 337, the conductor and half-point term
together cost at most 2.8865 for every Gaussian scale at least one. -/
theorem gaussian_shift_from334_197 {r s : ℝ} (hr : r ∈ Set.Icc 334 337) (hs : 1 ≤ s) :
    (-2.8865 : ℝ) ≤ gaussianTheta197 r / s + gaussianNegPole197 / r := by
  have hp : 0 < r := (by norm_num only : (0 : ℝ) < 334).trans_le hr.1
  have hθ : (-2.948 : ℝ) ≤ gaussianTheta197 r / s :=
    (le_div_iff₀ (zero_lt_one.trans_le hs)).mpr
      ((by linarith only [hs] : (-2.948 : ℝ) * s ≤ -2.948).trans (gaussian_theta_from334_197 hr.1))
  have hn : (0.0615 : ℝ) ≤ gaussianNegPole197 / r :=
    (le_div_iff₀ hp).mpr (by linarith only [hr.2, gaussian_neg_pole_lower_197])
  linarith only [hθ, hn]

/-- For every radius at least 333.8, the K197 conductor contribution is
bounded below by -2.949. Only the endpoint needs numerical certification. -/
theorem gaussian_theta_from3338_197 {r : ℝ} (hr : 333.8 ≤ r) :
    (-2.949 : ℝ) ≤ gaussianTheta197 r := by
  have hlo :=
    Analysis.rationalLogIntervalCheck_sound (N := 1669 / 5) (j := 9) (n := 27) (lo := 5.81) (hi :=
      5.81085) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hlo
  have hlog : (23 / 2 : ℝ) ≤ 2 * Real.log 333.8 := by linarith only [hlo.1]
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 1669 / 5) (p := 6) (d :=
        5) (lo := 0) (hi := 0.000937167) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat, neg_div] at hp
  rw [show (1669 / 5 : ℝ) = 333.8 by norm_num only] at hp
  have hP :=
    conductor_poly_mono (sub_nonneg.mpr hlog) (by norm_num only : (0 : ℝ) ≤ 0.1217)
      (show 2 * Real.log 333.8 - 23 / 2 ≤ 0.1217 by linarith only [hlo.2])
  have hprod :=
    (mul_le_mul_of_nonneg_left hP (Real.rpow_nonneg (by norm_num only) _)).trans
      (mul_le_mul_of_nonneg_right hp (by norm_num only [gaussianConductorPoly197]))
  apply gaussian_theta_endpoint_197 (by norm_num only) hr hlog
  rw [mul_assoc]
  refine
    (mul_le_mul_of_nonneg_left hprod (by norm_num only : (0 : ℝ) ≤ (11 / 10) ^ 5 / 30)).trans ?_
  norm_num only [gaussianConductorPoly197]

/-- On radii from 333.8 through 337, the conductor and half-point term
together cost at most 2.8875 for every Gaussian scale at least one. -/
theorem gaussian_shift_from3338_197 {r s : ℝ} (hr : r ∈ Set.Icc 333.8 337) (hs : 1 ≤ s) :
    (-2.8875 : ℝ) ≤ gaussianTheta197 r / s + gaussianNegPole197 / r := by
  have hp : 0 < r := (by norm_num only : (0 : ℝ) < 333.8).trans_le hr.1
  have hθ : (-2.949 : ℝ) ≤ gaussianTheta197 r / s :=
    (le_div_iff₀ (zero_lt_one.trans_le hs)).mpr
      ((by linarith only [hs] : (-2.949 : ℝ) * s ≤ -2.949).trans (gaussian_theta_from3338_197 hr.1))
  have hn : (0.0615 : ℝ) ≤ gaussianNegPole197 / r :=
    (le_div_iff₀ hp).mpr (by linarith only [hr.2, gaussian_neg_pole_lower_197])
  linarith only [hθ, hn]

/-- For every radius at least 336.8, the K197 conductor contribution is
bounded below by -2.934. Only the endpoint needs numerical certification. -/
theorem gaussian_theta_from3368_197 {r : ℝ} (hr : 336.8 ≤ r) :
    (-2.934 : ℝ) ≤ gaussianTheta197 r := by
  have hlo :=
    Analysis.rationalLogIntervalCheck_sound (N := 1684 / 5) (j := 9) (n := 27) (lo := 5.81) (hi :=
      5.81950) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hlo
  have hlog : (23 / 2 : ℝ) ≤ 2 * Real.log 336.8 := by linarith only [hlo.1]
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 1684 / 5) (p := 6) (d :=
        5) (lo := 0) (hi := 0.000927159) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat, neg_div] at hp
  rw [show (1684 / 5 : ℝ) = 336.8 by norm_num only] at hp
  have hP :=
    conductor_poly_mono (sub_nonneg.mpr hlog) (by norm_num only : (0 : ℝ) ≤ 0.139)
      (show 2 * Real.log 336.8 - 23 / 2 ≤ 0.139 by linarith only [hlo.2])
  have hprod :=
    (mul_le_mul_of_nonneg_left hP (Real.rpow_nonneg (by norm_num only) _)).trans
      (mul_le_mul_of_nonneg_right hp (by norm_num only [gaussianConductorPoly197]))
  apply gaussian_theta_endpoint_197 (by norm_num only) hr hlog
  rw [mul_assoc]
  refine
    (mul_le_mul_of_nonneg_left hprod (by norm_num only : (0 : ℝ) ≤ (11 / 10) ^ 5 / 30)).trans ?_
  norm_num only [gaussianConductorPoly197]

/-- For every radius at least 338, the K197 conductor contribution is
bounded below by -2.929. Only the endpoint needs numerical certification. -/
theorem gaussian_theta_from338_197 {r : ℝ} (hr : 338 ≤ r) : (-2.929 : ℝ) ≤ gaussianTheta197 r := by
  have hlo :=
    Analysis.rationalLogIntervalCheck_sound (N := 338) (j := 9) (n := 27) (lo := 5.81) (hi :=
      5.82305) (by decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_ofScientific] at hlo
  have hlog : (23 / 2 : ℝ) ≤ 2 * Real.log 338 := by linarith only [hlo.1]
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 338) (p := 6) (d := 5)
        (lo := 0) (hi := 0.000923210) (by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat, neg_div] at hp
  have hP :=
    conductor_poly_mono (sub_nonneg.mpr hlog) (by norm_num only : (0 : ℝ) ≤ 0.1461)
      (show 2 * Real.log 338 - 23 / 2 ≤ 0.1461 by linarith only [hlo.2])
  have hprod :=
    (mul_le_mul_of_nonneg_left hP (Real.rpow_nonneg (by norm_num only) _)).trans
      (mul_le_mul_of_nonneg_right hp (by norm_num only [gaussianConductorPoly197]))
  apply gaussian_theta_endpoint_197 (by norm_num only) hr hlog
  rw [mul_assoc]
  refine
    (mul_le_mul_of_nonneg_left hprod (by norm_num only : (0 : ℝ) ≤ (11 / 10) ^ 5 / 30)).trans ?_
  norm_num only [gaussianConductorPoly197]

end PseudoPrime.PrimeTestBounds.MillerRabin
