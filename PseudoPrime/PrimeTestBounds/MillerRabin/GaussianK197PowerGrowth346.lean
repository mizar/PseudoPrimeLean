/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197PowerBounds
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197PowerBounds
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197ConductorTail
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPrincipalTail663
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Shift

/-! # K197 power growth above radius 345.7 -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private theorem weight_growth_from340 {r n g : ℝ} (hr : 345.7 ≤ r)
    (hg : 0 ≤ Real.log r - Real.log 340)
    (hm : g ≤ 1 + 0.73 * (11 / 5) * (Real.log r - Real.log 340)) (hn : r ^ 2 ≤ n)
    (hs : Real.log (n / (340 : ℝ) ^ 2) ≤ 21 / 8) :
    g * quarterWeight656 ((340 : ℝ) ^ 2) n ≤ quarterWeight656 (r ^ 2) n := by
  have hr₀ : 0 < r := (by norm_num only : (0 : ℝ) < 345.7).trans_le hr
  have hn₀ := (sq_pos_of_pos hr₀).trans_le hn
  let v := (11 / 10 : ℝ) * (21 / 8 - Real.log (n / (340 : ℝ) ^ 2))
  let w := (11 / 10 : ℝ) * (21 / 8 - Real.log (n / r ^ 2))
  have hv : 0 ≤ v := by
    dsimp only [v]; linarith only [hs]
  have hln : 0 ≤ Real.log (n / r ^ 2) := Real.log_nonneg ((one_le_div (sq_pos_of_pos hr₀)).mpr hn)
  have hw : w ≤ 2.8875 := by
    dsimp only [w]; linarith only [hln]
  have he : w - v = (11 / 5) * (Real.log r - Real.log 340) := by
    dsimp only [v, w]
    rw [Real.log_div hn₀.ne' (sq_pos_of_pos hr₀).ne', Real.log_div hn₀.ne' (by norm_num only),
      Real.log_pow, Real.log_pow, Nat.cast_ofNat]
    ring
  have hf := forward_growth hv (by linarith only [he, hg] : v ≤ w) hw
  have hm' : g ≤ 1 + 0.73 * (w - v) := by linarith only [he, hm]
  have ht :=
    (mul_le_mul_of_nonneg_right hm' (mul_nonneg (pow_nonneg hv 5) (Real.exp_pos (-v)).le)).trans hf
  unfold quarterWeight656
  calc
    _ = (1 / Real.sqrt n) * ((g * (v ^ 5 * Real.exp (-v))) / 120) := by
      dsimp only [v]
      ring
    _ ≤ _ :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right ht (by norm_num only))
        (one_div_nonneg.mpr (Real.sqrt_nonneg _))

private theorem log_gain_from3457 {r : ℝ} (hr : 345.7 ≤ r) :
    0.01662 ≤ Real.log r - Real.log 340 := by
  have ha :=
    (Analysis.rationalLogIntervalCheck_sound (N := 3457 / 10) (j := 9) (n := 27) (lo := 5.84557)
        (hi := 6) (by decide +kernel)).1
  have hb :=
    (Analysis.rationalLogIntervalCheck_sound (N := 340) (j := 9) (n := 27) (lo := 5) (hi := 5.82895)
        (by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_ofScientific] at ha hb
  have hr' : (3457 / 10 : ℝ) ≤ r := by linarith only [hr]
  linarith only [ha, hb, Real.log_le_log (by norm_num only : (0 : ℝ) < 3457 / 10) hr']

private theorem grown_without343 {r : ℝ} (hr : r ∈ Set.Icc 345.7 346.1) :
    (0.1509 : ℝ) ≤
      ∑ n ∈ (fixedPowers663.erase (337 ^ 2)).erase (7 ^ 6),
        4 * (ArithmeticFunction.vonMangoldt n * quarterWeight656 (r ^ 2) n) := by
  have hl := log_gain_from3457 hr.1
  have h0 := retained_gain_without343 (r := 340) ⟨le_rfl, by norm_num only⟩
  refine (show (0.1509 : ℝ) ≤ 1.02669 * 0.147 by norm_num only).trans ?_
  refine (mul_le_mul_of_nonneg_left h0 (by norm_num only)).trans ?_
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  have hcut := retained_without343_cut ⟨(by norm_num only : (340 : ℝ) ≤ 345.7).trans hr.1, hr.2⟩ hn
  have hlog := retained_log_support (r := 340) (by norm_num only) (Finset.mem_of_mem_erase hn)
  have hw :=
    weight_growth_from340 hr.1 (g := 1.02669) (by linarith only [hl]) (by linarith only [hl])
      hcut.le hlog
  have h := mul_le_mul_of_nonneg_left hw (ArithmeticFunction.vonMangoldt_nonneg (n := n))
  linarith only [h]

private theorem radius_log_3457 : Real.log (3457 / 10 : ℝ) ∈ Set.Icc 5.84557 5.84558 := by
  have h :=
    Analysis.rationalLogIntervalCheck_sound (N := 3457 / 10) (j := 9) (n := 27) (lo := 5.84557)
      (hi := 5.84558) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at h ⊢
  exact h

private theorem radius_power_3457 : (3457 / 10 : ℝ) ^ (-(6 / 5) : ℝ) ≤ 0.00089859 := by
  have h :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 3457 / 10) (p := 6)
        (d := 5) (lo := 0) (hi := 0.00089859) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat,
    neg_div] at h ⊢
  exact h

/-- The shifted conductor term is at least -2.89212 at radii from 345.7. -/
theorem theta_from3457 {r : ℝ} (hr : (3457 / 10 : ℝ) ≤ r) :
    (-2.89212 : ℝ) ≤ gaussianTheta197 r := by
  have hlog : (23 / 2 : ℝ) ≤ 2 * Real.log (3457 / 10) := by linarith only [radius_log_3457.1]
  have hP :=
    conductor_poly_mono (sub_nonneg.mpr hlog) (by norm_num only : (0 : ℝ) ≤ 0.19116)
      (show 2 * Real.log (3457 / 10) - 23 / 2 ≤ 0.19116 by linarith only [radius_log_3457.2])
  have hprod :=
    (mul_le_mul_of_nonneg_left hP (Real.rpow_nonneg (by norm_num only) _)).trans
      (mul_le_mul_of_nonneg_right radius_power_3457 (by norm_num only [gaussianConductorPoly197]))
  apply gaussian_theta_endpoint_197 (by norm_num only) hr hlog
  rw [mul_assoc]
  exact
    (mul_le_mul_of_nonneg_left hprod (by norm_num only : (0 : ℝ) ≤ (11 / 10) ^ 5 / 30)).trans
      (by norm_num only [gaussianConductorPoly197])

/-- The principal inverse-scale conductor is bounded by its certified
value at radius 345.7 for all larger radii. -/
theorem quarter_main_conductor_from3457 {r : ℝ} (hr : (3457 / 10 : ℝ) ≤ r) :
    4 * r * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 1.61626 := by
  have hb :=
    main_conductor_box (r := 3457 / 10) (u := 3457 / 10) (z := 11.69116) (C := 1.61626)
      (by norm_num only) le_rfl (by linarith only [radius_log_3457.2]) radius_power_3457
      (by norm_num only) (by norm_num only)
  have hl : (3457 / 10 : ℝ) ∈ Set.Ici 328 := by norm_num only [Set.mem_Ici]
  have he := main_conductor_antitone hl (hl.trans hr) hr
  exact he.trans (by simpa only [sub_self, mul_zero, add_zero] using hb)

/-- The inverse-scale principal conductor is at most 1.61328 after
division by a Gaussian scale of at least 1.00185. -/
theorem gaussian_main_conductor_from3457 {r s : ℝ} (hr : (3457 / 10 : ℝ) ≤ r) (hs : 1.00185 ≤ s) :
    4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 1.61328 := by
  have hs₀ : 0 < s := (by norm_num only : (0 : ℝ) < 1.00185).trans_le hs
  rw [show
      4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re =
        (4 * r * (quarterKernel656.transform (r ^ 2)⁻¹).re) / s
      by ring]
  apply (div_le_iff₀ hs₀).mpr
  linarith only [quarter_main_conductor_from3457 hr, hs]

end PseudoPrime.PrimeTestBounds.MillerRabin
