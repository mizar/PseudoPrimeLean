/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterWindow576
import PseudoPrime.AnalyticNumberTheory.Arithmetic.TruncatedEulerCertificates3
import PseudoPrime.Analysis.LogTaylorBounds

/-! # Prime window transfer for section 99 -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Across the section 99 prime window the sixth-pole Euler weight dominates the
shifted triangle divided by the square root, with a common radius-dependent coefficient. -/
theorem prime_window_euler_600 {r : ℝ} (hl : 292 ≤ r) (hu : r ≤ 300) {p : ℕ} (hp : r ^ 2 ≤ p)
    (hw : Real.log p - 2 * Real.log r ≤ 5) :
    (13 / 200 * eulerLogPoly (2 * Real.log r) * r ^ (-(51 / 25 : ℝ))) *
        (shiftedTriangle (5 / 2) (Real.log p - 2 * Real.log r) / Real.sqrt p) ≤
      quarterEulerWeight570 p := by
  have hr : 0 < r := by linarith only [hl]
  have hpos := (sq_pos_of_pos hr).trans_le hp
  have hlog := Real.log_le_log (sq_pos_of_pos hr) hp
  rw [Real.log_pow, Nat.cast_ofNat] at hlog
  have h300 :=
    (Analysis.rationalLogIntervalCheck_sound (N := 300) (j := 8) (n := 24) (lo := 5) (hi :=
        571 / 100) (by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at h300
  have ht :=
    window_weight_lower_600 (v := 2 * Real.log r) (x := Real.log p - 2 * Real.log r)
      (mul_nonneg (by norm_num only) (Real.log_nonneg (by linarith only [hl])))
      (sub_nonneg.mpr hlog) (by linarith only [hw, Real.log_le_log hr hu, h300])
  rw [show 2 * Real.log r + (Real.log p - 2 * Real.log r) = Real.log p by ring] at ht
  have hs :=
    mul_le_mul_of_nonneg_right ht (show 0 ≤ r ^ (-(51 / 25 : ℝ)) / Real.sqrt p by positivity)
  have he :
    Real.exp (-(51 / 50) * (Real.log p - 2 * Real.log r)) * (r ^ (-(51 / 25 : ℝ)) / Real.sqrt p) =
      ((p : ℝ) ^ (38 / 25 : ℝ))⁻¹ := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hr, Real.rpow_def_of_pos hpos,
      Real.rpow_def_of_pos hpos, ← Real.exp_sub, ← Real.exp_neg, ← Real.exp_add]
    congr 1
    ring
  rw [show quarterEulerWeight570 p = eulerLogPoly (Real.log p) / (p : ℝ) ^ (38 / 25 : ℝ) by
      unfold quarterEulerWeight570 eulerLogPoly; ring]
  convert hs using 1
  · ring
  · rw [mul_right_comm _ (eulerLogPoly _) _, he]
    ring

/-- Summing the pointwise comparison with nonnegative logarithmic weights bounds
the triangle mass of any finite subset of the window by its Euler contribution. -/
theorem sum_window_euler_600 {r : ℝ} (hl : 292 ≤ r) (hu : r ≤ 300) (s : Finset ℕ)
    (hp : ∀ p ∈ s, r ^ 2 ≤ (p : ℝ)) (hw : ∀ p ∈ s, Real.log p - 2 * Real.log r ≤ 5) :
    (13 / 200 * eulerLogPoly (2 * Real.log r) * r ^ (-(51 / 25 : ℝ))) *
        ∑ p ∈ s,
          Real.log p * (shiftedTriangle (5 / 2) (Real.log p - 2 * Real.log r) / Real.sqrt p) ≤
      ∑ p ∈ s, Real.log p * quarterEulerWeight570 p := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p h
  rw [mul_left_comm]
  exact
    mul_le_mul_of_nonneg_left (prime_window_euler_600 hl hu (hp p h) (hw p h))
      (Real.log_natCast_nonneg p)

/-- The fourfold window coefficient is bounded below by freezing the
logarithmic polynomial at a left endpoint and the power at a right endpoint. -/
private theorem window_factor_endpoint_600 {r V P : ℝ} (hr : 0 < r) (hV : 0 ≤ V)
    (hv : V ≤ 2 * Real.log r) (hP : 0 ≤ P) (hp : P ≤ r ^ (-(26 / 25 : ℝ))) :
    4 * (13 / 200 : ℝ) * (73 / 50) * (eulerLogPoly V * P) ≤
      4 * (13 / 200 * eulerLogPoly (2 * Real.log r) * r ^ (-(51 / 25 : ℝ))) * (73 / 50 * r) := by
  have hq : eulerLogPoly V ≤ eulerLogPoly (2 * Real.log r) := by
    unfold eulerLogPoly
    have hsq := pow_le_pow_left₀ hV hv 2
    linarith only [hv, hsq]
  have hn : 0 ≤ eulerLogPoly (2 * Real.log r) := by
    unfold eulerLogPoly
    have h := hV.trans hv
    positivity
  have hm := mul_le_mul hq hp hP hn
  have he : r ^ (-(51 / 25 : ℝ)) * r = r ^ (-(26 / 25 : ℝ)) := by
    calc
      _ = r ^ (-(51 / 25 : ℝ)) * r ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = _ := by
        rw [← Real.rpow_add hr]; norm_num only
  rw [show
      4 * (13 / 200 * eulerLogPoly (2 * Real.log r) * r ^ (-(51 / 25 : ℝ))) * (73 / 50 * r) =
        (4 * (13 / 200) * (73 / 50)) * (eulerLogPoly (2 * Real.log r) * (r ^ (-(51 / 25 : ℝ)) * r))
      by ring,
    he]
  exact mul_le_mul_of_nonneg_left hm (by norm_num only)

/-- In the two section 99 ranges the triangle mass coefficient gives
the certified savings 0.02169 and 0.02179, respectively. -/
theorem window_factor_gt_600 {r : ℝ} (hl : 292 ≤ r) (hu : r ≤ 300) :
    (if r ≤ 299 then 0.02169 else 0.02179) <
      4 * (13 / 200 * eulerLogPoly (2 * Real.log r) * r ^ (-(51 / 25 : ℝ))) * (73 / 50 * r) := by
  have hr : 0 < r := by linarith only [hl]
  split_ifs with h
  · have hlog :=
      (Analysis.rationalLogIntervalCheck_sound (N := 292) (j := 8) (n := 24) (lo := 227 / 40) (hi :=
          6) (by decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlog
    have hv : (227 / 20 : ℝ) ≤ 2 * Real.log r := by
      linarith only [hlog, Real.log_le_log (by norm_num only) hl]
    have hb :=
      (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 299) (p := 26) (d :=
          25) (lo := 26625 / 10000000) (hi := 1) (by decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at hb
    exact
      (by norm_num only [eulerLogPoly] :
            (0.02169 : ℝ) <
              4 * (13 / 200) * (73 / 50) * (eulerLogPoly (227 / 20) * (26625 / 10000000))).trans_le
        (window_factor_endpoint_600 hr (by norm_num only) hv (by norm_num only)
          (by
            apply le_trans _ (Real.rpow_le_rpow_of_nonpos hr h (by norm_num only))
            linarith only [hb]))
  · have hl' : 299 ≤ r := le_of_not_ge h
    have hlog :=
      (Analysis.rationalLogIntervalCheck_sound (N := 299) (j := 8) (n := 24) (lo := 57 / 10) (hi :=
          6) (by decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlog
    have hv : (57 / 5 : ℝ) ≤ 2 * Real.log r := by
      linarith only [hlog, Real.log_le_log (by norm_num only) hl']
    have hb :=
      (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 300) (p := 26) (d :=
          25) (lo := 26533 / 10000000) (hi := 1) (by decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at hb
    exact
      (by norm_num only [eulerLogPoly] :
            (0.02179 : ℝ) <
              4 * (13 / 200) * (73 / 50) * (eulerLogPoly (57 / 5) * (26533 / 10000000))).trans_le
        (window_factor_endpoint_600 hr (by norm_num only) hv (by norm_num only)
          (by
            apply le_trans _ (Real.rpow_le_rpow_of_nonpos hr hu (by norm_num only))
            linarith only [hb]))

/-- A finite window with triangle mass at least 1.46 times the radius saves more
than 0.02169 through radius 299 and 0.02179 thereafter in section 99. -/
theorem window_euler_saving_600 {r : ℝ} (hl : 292 ≤ r) (hu : r ≤ 300) (s : Finset ℕ)
    (hp : ∀ p ∈ s, r ^ 2 ≤ (p : ℝ)) (hw : ∀ p ∈ s, Real.log p - 2 * Real.log r ≤ 5)
    (hm :
      73 / 50 * r ≤
        ∑ p ∈ s,
          Real.log p * (shiftedTriangle (5 / 2) (Real.log p - 2 * Real.log r) / Real.sqrt p)) :
    (if r ≤ 299 then 0.02169 else 0.02179) < 4 * ∑ p ∈ s, Real.log p * quarterEulerWeight570 p := by
  have hlog := Real.log_nonneg (show 1 ≤ r by linarith only [hl])
  have hq : 0 ≤ eulerLogPoly (2 * Real.log r) := by
    unfold eulerLogPoly; positivity
  have ha :=
    mul_le_mul_of_nonneg_left hm
      (show 0 ≤ 13 / 200 * eulerLogPoly (2 * Real.log r) * r ^ (-(51 / 25 : ℝ)) by positivity)
  have hb := ha.trans (sum_window_euler_600 hl hu s hp hw)
  linarith only [window_factor_gt_600 hl hu, hb]

end PseudoPrime.PrimeTestBounds.MillerRabin
