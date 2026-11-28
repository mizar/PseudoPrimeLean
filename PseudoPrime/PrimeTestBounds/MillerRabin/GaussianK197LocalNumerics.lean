/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Shift
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Shift
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197ConductorTail
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPrincipalTail663

/-! # K197 conductor bounds for radii starting at 338.36 -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private theorem radius_log_33836 : Real.log (8459 / 25 : ℝ) ∈ Set.Icc 5.82410 5.82412 := by
  have h :=
    Analysis.rationalLogIntervalCheck_sound (N := 8459 / 25) (j := 9) (n := 27) (lo := 5.82410)
      (hi := 5.82412) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at h ⊢
  exact h

private theorem radius_power_33836 : (8459 / 25 : ℝ) ^ (-(6 / 5) : ℝ) ≤ 0.000922032 := by
  have h :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 8459 / 25) (p := 6)
        (d := 5) (lo := 0) (hi := 0.000922032) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat,
    neg_div] at h ⊢
  exact h

/-- The shifted conductor term is at least -2.9266 at radii from 338.36. -/
theorem theta_from33836 {r : ℝ} (hr : (8459 / 25 : ℝ) ≤ r) :
    (-2.9266 : ℝ) ≤ gaussianTheta197 r := by
  have hlog : (23 / 2 : ℝ) ≤ 2 * Real.log (8459 / 25) := by linarith only [radius_log_33836.1]
  have hP :=
    conductor_poly_mono (sub_nonneg.mpr hlog) (by norm_num only : (0 : ℝ) ≤ 0.14824)
      (show 2 * Real.log (8459 / 25) - 23 / 2 ≤ 0.14824 by linarith only [radius_log_33836.2])
  have hprod :=
    (mul_le_mul_of_nonneg_left hP (Real.rpow_nonneg (by norm_num only) _)).trans
      (mul_le_mul_of_nonneg_right radius_power_33836 (by norm_num only [gaussianConductorPoly197]))
  apply gaussian_theta_endpoint_197 (by norm_num only) hr hlog
  rw [mul_assoc]
  exact
    (mul_le_mul_of_nonneg_left hprod (by norm_num only : (0 : ℝ) ≤ (11 / 10) ^ 5 / 30)).trans
      (by norm_num only [gaussianConductorPoly197])

/-- The principal inverse-scale conductor is bounded by its certified
value at radius 338.36 for all larger radii. -/
theorem quarter_main_conductor_from33836 {r : ℝ} (hr : (8459 / 25 : ℝ) ≤ r) :
    4 * r * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 1.63374 := by
  have hb :=
    main_conductor_box (r := 8459 / 25) (u := 8459 / 25) (z := 11.64824) (C := 1.63374)
      (by norm_num only) le_rfl (by linarith only [radius_log_33836.2]) radius_power_33836
      (by norm_num only) (by norm_num only)
  have hl : (8459 / 25 : ℝ) ∈ Set.Ici 328 := by norm_num only [Set.mem_Ici]
  have he := main_conductor_antitone hl (hl.trans hr) hr
  exact he.trans (by simpa only [sub_self, mul_zero, add_zero] using hb)

private theorem radius_log_3394 : Real.log (1697 / 5 : ℝ) ∈ Set.Icc 5.82717 5.82719 := by
  have h :=
    Analysis.rationalLogIntervalCheck_sound (N := 1697 / 5) (j := 9) (n := 27) (lo := 5.82717)
      (hi := 5.82719) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at h ⊢
  exact h

private theorem radius_power_3394 : (1697 / 5 : ℝ) ^ (-(6 / 5) : ℝ) ≤ 0.000918642 := by
  have h :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 1697 / 5) (p := 6) (d :=
        5) (lo := 0) (hi := 0.000918642) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat,
    neg_div] at h ⊢
  exact h

/-- The shifted conductor term is at least -2.92155 at radii from 339.4. -/
theorem theta_from3394 {r : ℝ} (hr : (1697 / 5 : ℝ) ≤ r) : (-2.92155 : ℝ) ≤ gaussianTheta197 r := by
  have hlog : (23 / 2 : ℝ) ≤ 2 * Real.log (1697 / 5) := by linarith only [radius_log_3394.1]
  have hP :=
    conductor_poly_mono (sub_nonneg.mpr hlog) (by norm_num only : (0 : ℝ) ≤ 0.15438)
      (show 2 * Real.log (1697 / 5) - 23 / 2 ≤ 0.15438 by linarith only [radius_log_3394.2])
  have hprod :=
    (mul_le_mul_of_nonneg_left hP (Real.rpow_nonneg (by norm_num only) _)).trans
      (mul_le_mul_of_nonneg_right radius_power_3394 (by norm_num only [gaussianConductorPoly197]))
  apply gaussian_theta_endpoint_197 (by norm_num only) hr hlog
  rw [mul_assoc]
  exact
    (mul_le_mul_of_nonneg_left hprod (by norm_num only : (0 : ℝ) ≤ (11 / 10) ^ 5 / 30)).trans
      (by norm_num only [gaussianConductorPoly197])

private theorem radius_log_33979 : Real.log (33979 / 100 : ℝ) ∈ Set.Icc 5.82832 5.82834 := by
  have h :=
    Analysis.rationalLogIntervalCheck_sound (N := 33979 / 100) (j := 9) (n := 27) (lo := 5.82832)
      (hi := 5.82834) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at h ⊢
  exact h

private theorem radius_power_33979 : (33979 / 100 : ℝ) ^ (-(6 / 5) : ℝ) ≤ 0.000917377 := by
  have h :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 33979 / 100) (p := 6)
        (d := 5) (lo := 0) (hi := 0.000917377) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat,
    neg_div] at h ⊢
  exact h

/-- The shifted conductor term is at least -2.91972 at radii from 339.79. -/
theorem theta_from33979 {r : ℝ} (hr : (33979 / 100 : ℝ) ≤ r) :
    (-2.91972 : ℝ) ≤ gaussianTheta197 r := by
  have hlog : (23 / 2 : ℝ) ≤ 2 * Real.log (33979 / 100) := by linarith only [radius_log_33979.1]
  have hP :=
    conductor_poly_mono (sub_nonneg.mpr hlog) (by norm_num only : (0 : ℝ) ≤ 0.15668)
      (show 2 * Real.log (33979 / 100) - 23 / 2 ≤ 0.15668 by linarith only [radius_log_33979.2])
  have hprod :=
    (mul_le_mul_of_nonneg_left hP (Real.rpow_nonneg (by norm_num only) _)).trans
      (mul_le_mul_of_nonneg_right radius_power_33979 (by norm_num only [gaussianConductorPoly197]))
  apply gaussian_theta_endpoint_197 (by norm_num only) hr hlog
  rw [mul_assoc]
  exact
    (mul_le_mul_of_nonneg_left hprod (by norm_num only : (0 : ℝ) ≤ (11 / 10) ^ 5 / 30)).trans
      (by norm_num only [gaussianConductorPoly197])

/-- The principal inverse-scale conductor is bounded by its certified
value at radius 339.79 for all larger radii. -/
theorem quarter_main_conductor_from33979 {r : ℝ} (hr : (33979 / 100 : ℝ) ≤ r) :
    4 * r * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 1.63028 := by
  have hb :=
    main_conductor_box (r := 33979 / 100) (u := 33979 / 100) (z := 11.65668) (C := 1.63028)
      (by norm_num only) le_rfl (by linarith only [radius_log_33979.2]) radius_power_33979
      (by norm_num only) (by norm_num only)
  have hl : (33979 / 100 : ℝ) ∈ Set.Ici 328 := by norm_num only [Set.mem_Ici]
  have he := main_conductor_antitone hl (hl.trans hr) hr
  exact he.trans (by simpa only [sub_self, mul_zero, add_zero] using hb)

private theorem radius_log_339916 : Real.log (339916 / 1000 : ℝ) ∈ Set.Icc 5.82869 5.82870 := by
  have h :=
    Analysis.rationalLogIntervalCheck_sound (N := 339916 / 1000) (j := 9) (n := 27) (lo := 5.82869)
      (hi := 5.82870) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at h ⊢
  exact h

private theorem radius_power_339916 : (339916 / 1000 : ℝ) ^ (-(6 / 5) : ℝ) ≤ 0.000916969 := by
  have h :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 339916 / 1000) (p := 6)
        (d := 5) (lo := 0) (hi := 0.000916969) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat,
    neg_div] at h ⊢
  exact h

/-- The shifted conductor term is at least -2.91911 at radii from 339.916. -/
theorem theta_from339916 {r : ℝ} (hr : (339916 / 1000 : ℝ) ≤ r) :
    (-2.91911 : ℝ) ≤ gaussianTheta197 r := by
  have hlog : (23 / 2 : ℝ) ≤ 2 * Real.log (339916 / 1000) := by linarith only [radius_log_339916.1]
  have hP :=
    conductor_poly_mono (sub_nonneg.mpr hlog) (by norm_num only : (0 : ℝ) ≤ 0.15740)
      (show 2 * Real.log (339916 / 1000) - 23 / 2 ≤ 0.15740 by linarith only [radius_log_339916.2])
  have hprod :=
    (mul_le_mul_of_nonneg_left hP (Real.rpow_nonneg (by norm_num only) _)).trans
      (mul_le_mul_of_nonneg_right radius_power_339916 (by norm_num only [gaussianConductorPoly197]))
  apply gaussian_theta_endpoint_197 (by norm_num only) hr hlog
  rw [mul_assoc]
  exact
    (mul_le_mul_of_nonneg_left hprod (by norm_num only : (0 : ℝ) ≤ (11 / 10) ^ 5 / 30)).trans
      (by norm_num only [gaussianConductorPoly197])

/-- The principal inverse-scale conductor is bounded by its certified
value at radius 339.916 for all larger radii. -/
theorem quarter_main_conductor_from339916 {r : ℝ} (hr : (339916 / 1000 : ℝ) ≤ r) :
    4 * r * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 1.62997 := by
  have hb :=
    main_conductor_box (r := 339916 / 1000) (u := 339916 / 1000) (z := 11.65740) (C := 1.62997)
      (by norm_num only) le_rfl (by linarith only [radius_log_339916.2]) radius_power_339916
      (by norm_num only) (by norm_num only)
  have hl : (339916 / 1000 : ℝ) ∈ Set.Ici 328 := by norm_num only [Set.mem_Ici]
  have he := main_conductor_antitone hl (hl.trans hr) hr
  exact he.trans (by simpa only [sub_self, mul_zero, add_zero] using hb)

private theorem radius_log_34549 : Real.log (34549 / 100 : ℝ) ∈ Set.Icc 5.84496 5.84497 := by
  have h :=
    Analysis.rationalLogIntervalCheck_sound (N := 34549 / 100) (j := 9) (n := 27) (lo := 5.84496)
      (hi := 5.84497) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at h ⊢
  exact h

private theorem radius_power_34549 : (34549 / 100 : ℝ) ^ (-(6 / 5) : ℝ) ≤ 0.000899245 := by
  have h :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 34549 / 100) (p := 6)
        (d := 5) (lo := 0) (hi := 0.000899245) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat,
    neg_div] at h ⊢
  exact h

/-- The shifted conductor term is at least -2.89309 at radii from 345.49. -/
theorem theta_from34549 {r : ℝ} (hr : (34549 / 100 : ℝ) ≤ r) :
    (-2.89309 : ℝ) ≤ gaussianTheta197 r := by
  have hlog : (23 / 2 : ℝ) ≤ 2 * Real.log (34549 / 100) := by linarith only [radius_log_34549.1]
  have hP :=
    conductor_poly_mono (sub_nonneg.mpr hlog) (by norm_num only : (0 : ℝ) ≤ 0.18994)
      (show 2 * Real.log (34549 / 100) - 23 / 2 ≤ 0.18994 by linarith only [radius_log_34549.2])
  have hprod :=
    (mul_le_mul_of_nonneg_left hP (Real.rpow_nonneg (by norm_num only) _)).trans
      (mul_le_mul_of_nonneg_right radius_power_34549 (by norm_num only [gaussianConductorPoly197]))
  apply gaussian_theta_endpoint_197 (by norm_num only) hr hlog
  rw [mul_assoc]
  exact
    (mul_le_mul_of_nonneg_left hprod (by norm_num only : (0 : ℝ) ≤ (11 / 10) ^ 5 / 30)).trans
      (by norm_num only [gaussianConductorPoly197])

/-- The principal inverse-scale conductor is bounded by its certified
value at radius 345.49 for all larger radii. -/
theorem quarter_main_conductor_from34549 {r : ℝ} (hr : (34549 / 100 : ℝ) ≤ r) :
    4 * r * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 1.61675 := by
  have hb :=
    main_conductor_box (r := 34549 / 100) (u := 34549 / 100) (z := 11.68994) (C := 1.61675)
      (by norm_num only) le_rfl (by linarith only [radius_log_34549.2]) radius_power_34549
      (by norm_num only) (by norm_num only)
  have hl : (34549 / 100 : ℝ) ∈ Set.Ici 328 := by norm_num only [Set.mem_Ici]
  have he := main_conductor_antitone hl (hl.trans hr) hr
  exact he.trans (by simpa only [sub_self, mul_zero, add_zero] using hb)

private theorem local_shift_cost {r s u D : ℝ} (hr : r ∈ Set.Icc (8459 / 25) u) (hD : 0 ≤ D)
    (hDu : D * u ≤ 20.74) (hs : 1.00106 ≤ s) {T : ℝ} (hT : T ≤ gaussianTheta197 r)
    (hTs : ∀ t : ℝ, 1.00106 ≤ t → (T / 1.00106) * t ≤ T) :
    (T / 1.00106 + D : ℝ) ≤ gaussianTheta197 r / s + gaussianNegPole197 / r := by
  have hp : 0 < r := (by norm_num only : (0 : ℝ) < 8459 / 25).trans_le hr.1
  have hs₀ : 0 < s := (by norm_num only : (0 : ℝ) < 1.00106).trans_le hs
  have hθ : T / 1.00106 ≤ gaussianTheta197 r / s := (le_div_iff₀ hs₀).mpr ((hTs s hs).trans hT)
  have hn : D ≤ gaussianNegPole197 / r :=
    (le_div_iff₀ hp).mpr
      ((mul_le_mul_of_nonneg_left hr.2 hD).trans (hDu.trans gaussian_neg_pole_lower_197))
  linarith only [hθ, hn]

/-- The inverse-scale principal conductor is at most 1.63203 after
division by a Gaussian scale of at least 1.00106. -/
theorem gaussian_main_conductor_local_197 {r s : ℝ} (hr : (8459 / 25 : ℝ) ≤ r) (hs : 1.00106 ≤ s) :
    4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 1.63203 := by
  have hs₀ : 0 < s := (by norm_num only : (0 : ℝ) < 1.00106).trans_le hs
  rw [show
      4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re =
        (4 * r * (quarterKernel656.transform (r ^ 2)⁻¹).re) / s
      by ring]
  apply (div_le_iff₀ hs₀).mpr
  linarith only [quarter_main_conductor_from33836 hr, hs]

/-- The inverse-scale principal conductor is at most 1.62856 after
division by a Gaussian scale of at least 1.00106. -/
theorem gaussian_main_conductor_from33979 {r s : ℝ} (hr : (33979 / 100 : ℝ) ≤ r)
    (hs : 1.00106 ≤ s) : 4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 1.62856 := by
  have hs₀ : 0 < s := (by norm_num only : (0 : ℝ) < 1.00106).trans_le hs
  rw [show
      4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re =
        (4 * r * (quarterKernel656.transform (r ^ 2)⁻¹).re) / s
      by ring]
  apply (div_le_iff₀ hs₀).mpr
  linarith only [quarter_main_conductor_from33979 hr, hs]

/-- The inverse-scale principal conductor is at most 1.62825 after
division by a Gaussian scale of at least 1.00106. -/
theorem gaussian_main_conductor_from339916 {r s : ℝ} (hr : (339916 / 1000 : ℝ) ≤ r)
    (hs : 1.00106 ≤ s) : 4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 1.62825 := by
  have hs₀ : 0 < s := (by norm_num only : (0 : ℝ) < 1.00106).trans_le hs
  rw [show
      4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re =
        (4 * r * (quarterKernel656.transform (r ^ 2)⁻¹).re) / s
      by ring]
  apply (div_le_iff₀ hs₀).mpr
  linarith only [quarter_main_conductor_from339916 hr, hs]

/-- The inverse-scale principal conductor is at most 1.61504 after
division by a Gaussian scale of at least 1.00106. -/
theorem gaussian_main_conductor_from34549 {r s : ℝ} (hr : (34549 / 100 : ℝ) ≤ r)
    (hs : 1.00106 ≤ s) : 4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 1.61504 := by
  have hs₀ : 0 < s := (by norm_num only : (0 : ℝ) < 1.00106).trans_le hs
  rw [show
      4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re =
        (4 * r * (quarterKernel656.transform (r ^ 2)⁻¹).re) / s
      by ring]
  apply (div_le_iff₀ hs₀).mpr
  linarith only [quarter_main_conductor_from34549 hr, hs]

/-- For the radius block starting at 338.36 the three shifted forward terms and the
positive half-point contribution are bounded below using the supplied conductor estimate. -/
theorem gaussian_shift_forward_local_197 {p q k : ℕ} [NeZero p] [NeZero q] [NeZero k]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ k}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hRH : RiemannHypothesis) {r s u D : ℝ}
    (hr : r ∈ Set.Icc (8459 / 25) u) (hD : 0 ≤ D) (hDu : D * u ≤ 20.74) (hu : u ≤ 346.1)
    (hs : 1.00106 ≤ s) {T P : ℝ} (hT : T ≤ gaussianTheta197 r)
    (hTs : ∀ t : ℝ, 1.00106 ≤ t → (T / 1.00106) * t ≤ T) (hP : P ≤ T / 1.00106 + D - 0.000069)
    (hL : Real.log p + Real.log q + Real.log k = 4 * r / s)
    (ht : ∀ n : ℕ, (a n).re + (b n).re + (c n).re ∈ Set.Icc (-1) 3)
    (hpa : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → a l = 1)
    (hpb : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → b l = 1)
    (hpc : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → c l = 1) :
    P ≤
      (gaussianShiftedForward197 a r + gaussianShiftedForward197 b r +
          gaussianShiftedForward197 c r) +
        gaussianHalfCoeff197 * r := by
  have hwide : r ∈ Set.Icc 332.15 346.1 :=
    ⟨(by norm_num only : (332.15 : ℝ) ≤ 8459 / 25).trans hr.1, hr.2.trans hu⟩
  have h :=
    shift_forward_of_refl ha hb hc hRH ((by norm_num only : (328 : ℝ) ≤ 8459 / 25).trans hr.1) hL ht
      hpa hpb hpc (local_shift_cost hr hD hDu hs hT hTs) (gaussian_joint_to34610 hRH hwide)
  linarith only [h, hP]

end PseudoPrime.PrimeTestBounds.MillerRabin
