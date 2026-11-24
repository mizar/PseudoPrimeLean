/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLowerMidpoint
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevPhaseDefect
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Scalar lower bound on a logarithmic theta phase cell -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The smoothing ratio decreases from any left endpoint at least two. -/
private theorem ratio_le_left {a L : ℝ} (ha : 2 ≤ a) (hL : a ≤ L) :
    L / Real.exp (L / 2) ≤ a / Real.exp (a / 2) := by
  have he := Real.add_one_le_exp ((L - a) / 2)
  have hp := mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hL)
  have hm := mul_le_mul_of_nonneg_left he (show 0 ≤ a by linarith only [ha])
  have h : L ≤ a * Real.exp ((L - a) / 2) := by nlinarith only [hm, hp]
  apply (div_le_div_iff₀ (Real.exp_pos _) (Real.exp_pos _)).mpr
  have hsum : (L - a) / 2 + a / 2 = L / 2 := by ring
  simpa only [mul_assoc, ← Real.exp_add, hsum] using
    mul_le_mul_of_nonneg_right h (Real.exp_pos (a / 2)).le

private def expLower (a : ℚ) : ℚ :=
  (Finset.range 56).sum (fun i => (a / 2) ^ i / i.factorial)

private theorem cap_of_ticks (a D : ℚ) (ha : 0 ≤ a) (hd : 0 ≤ D) (h : a ≤ 4 * D * expLower a) :
    (a : ℝ) / Real.exp (a / 2) / 4 ≤ D := by
  have he :=
    Real.sum_le_exp_of_nonneg (x := (a : ℝ) / 2) (div_nonneg (by exact_mod_cast ha) zero_le_two) 56
  have hc : (expLower a : ℝ) ≤ Real.exp (a / 2) := by
    simpa only [expLower, Rat.cast_sum, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast,
      Rat.cast_ofNat] using he
  have hr : (a : ℝ) ≤ 4 * (D : ℝ) * (expLower a : ℝ) := by exact_mod_cast h
  have hd' : 0 ≤ (D : ℝ) := by exact_mod_cast hd
  have hm := mul_le_mul_of_nonneg_left hc (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 4) hd')
  apply (div_le_iff₀ (by norm_num only : (0 : ℝ) < 4)).mpr
  apply (div_le_iff₀ (Real.exp_pos _)).mpr
  linarith only [hr, hm]

/-- A Taylor lower bound at a rational argument certifies decay throughout a cell. -/
private theorem decay_tick (q U : ℚ) {z : ℝ} (hq : 0 ≤ q) (hu : 0 ≤ U) (hz : (q : ℝ) ≤ z)
    (hc : 1 ≤ U * expLower (2 * q)) : Real.exp (-z) ≤ (U : ℝ) := by
  have he := Real.sum_le_exp_of_nonneg (by exact_mod_cast hq : 0 ≤ (q : ℝ)) 56
  have hl : (expLower (2 * q) : ℝ) ≤ Real.exp (q : ℝ) := by
    simpa only [expLower, mul_div_cancel_left₀ q (by decide : (2 : ℚ) ≠ 0), Rat.cast_sum,
      Rat.cast_div, Rat.cast_pow, Rat.cast_natCast] using he
  have hr := (Rat.cast_le (K := ℝ)).2 hc
  rw [Rat.cast_one, Rat.cast_mul] at hr
  rw [Real.exp_neg, ← one_div, div_le_iff₀ (Real.exp_pos z)]
  exact
    hr.trans (mul_le_mul_of_nonneg_left (hl.trans (Real.exp_le_exp.mpr hz)) (by exact_mod_cast hu))

/-- Bound the cutoff logarithm from below using the tangent inequality at 18. -/
private theorem log_floor_eighteen {z : ℝ} (hz : 0 < z) :
    0.6931471803 + 2 * 1.0986122885 + 1 - 18 / z ≤ Real.log z := by
  have h := Real.one_sub_inv_le_log_of_pos (div_pos hz (show (0 : ℝ) < 18 by norm_num only))
  rw [inv_div, Real.log_div hz.ne' (by norm_num only : (18 : ℝ) ≠ 0)] at h
  have he : Real.log 18 = Real.log 2 + 2 * Real.log 3 := by
    calc
      Real.log 18 = Real.log (2 * (3 : ℝ) ^ 2) := by norm_num only
      _ = _ := by
        rw [Real.log_mul (by norm_num only) (by norm_num only), Real.log_pow, Nat.cast_ofNat]
  linarith only [h, he, Real.log_two_gt_d9, Real.log_three_gt_d9]

/-- Bound the cutoff logarithm using a positive lower bound for its denominator. -/
private theorem cutoff_log_cap {L z d b : ℝ} (hz : 0 < z) (hd : z ≤ d) (hb : L ≤ b) :
    Real.log (Real.exp (L / 2) / d) ≤ b / 2 - (0.6931471803 + 2 * 1.0986122885 + 1 - 18 / z) := by
  rw [Real.log_div (Real.exp_pos _).ne' (hz.trans_le hd).ne', Real.log_exp]
  have h := (log_floor_eighteen hz).trans (Real.log_le_log hz hd)
  linarith only [hb, h]

/-- Express the smoothing cutoff in the form used by the cell logarithm bound. -/
private theorem cutoff_ratio {L : ℝ} (hL : 0 < L) :
    (2 / (L / Real.exp (L / 2) / 4)) / (2 * Real.pi) = Real.exp (L / 2) / (L * Real.pi / 4) := by
  field_simp [hL.ne', Real.pi_ne_zero, (Real.exp_pos (L / 2)).ne']

/-- Bound the logarithm of the actual smoothing cutoff throughout one cell. -/
private theorem cell_cutoff_cap {a L b : ℝ} (ha : 0 < a) (hl : a ≤ L) (hr : L ≤ b) :
    Real.log ((2 / (L / Real.exp (L / 2) / 4)) / (2 * Real.pi)) ≤
      b / 2 - (0.6931471803 + 2 * 1.0986122885 + 1 - 18 / (a * (6283 / 8000))) := by
  rw [cutoff_ratio (ha.trans_le hl)]
  apply cutoff_log_cap (mul_pos ha (by norm_num only)) _ hr
  have hp : (6283 / 8000 : ℝ) ≤ Real.pi / 4 := by linarith only [Real.pi_gt_d4]
  calc
    _ ≤ L * (Real.pi / 4) := mul_le_mul hl hp (by norm_num only) (ha.trans_le hl).le
    _ = _ := by ring

/-- A rational cap on the logarithm bounds the whole reciprocal-zero tail. -/
private theorem tail_of_cutoff_cap {T v c : ℝ} (hT : 1 ≤ T) (hv : 0 ≤ v) (hc : v ≤ c) :
    (v ^ 2 + 2 * v + 2) / (2 * Real.pi) - 143 / 125 - (3 / 8) / T + 1 / (15 * T ^ 2) ≤
      (c ^ 2 + 2 * c + 2) / (6283 / 1000) - 143 / 125 := by
  have hpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have ht : 1 / (15 * T ^ 2) ≤ (3 / 8) / T := by
    apply (div_le_div_iff₀ (mul_pos (by norm_num only) (sq_pos_of_pos hpos)) hpos).2
    nlinarith only [mul_nonneg hpos.le (sub_nonneg.mpr hT), hpos.le]
  have hn : v ^ 2 + 2 * v + 2 ≤ c ^ 2 + 2 * c + 2 := by
    nlinarith only [sq_le_sq' (by linarith only [hv, hc] : -c ≤ v) hc, hc]
  have hd : (6283 / 1000 : ℝ) ≤ 2 * Real.pi := by linarith only [Real.pi_gt_d4]
  have hq :=
    div_le_div₀ (by nlinarith only [sq_nonneg c, hv, hc] : 0 ≤ c ^ 2 + 2 * c + 2) hn
      (by norm_num only : (0 : ℝ) < 6283 / 1000) hd
  linarith only [ht, hq]

/-- Normalize half the smoothing width exactly by the square root of the center. -/
private theorem half_width_eq (L : ℝ) :
    let x := Real.exp L
    let a := x - x * (L / Real.exp (L / 2) / 4)
    (x - a) / 2 / Real.sqrt x = L / 8 := by
  dsimp only
  have hs : Real.sqrt (Real.exp L) = Real.exp (L / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.exp_mul]
    congr 1
    ring
  rw [hs, sub_sub_cancel,
    show Real.exp L = Real.exp (L / 2) * Real.exp (L / 2) by
      rw [← Real.exp_add]; congr 1; ring]
  field_simp [(Real.exp_pos (L / 2)).ne']
  ring

/-- Positive smoothing widths of at least one contribute at most one before normalization. -/
private theorem smooth_constants_le {w x E : ℝ} (hw : 1 ≤ w) (hx : 0 < Real.sqrt x)
    (he : 1 / Real.sqrt x ≤ E) : (Real.log (2 * Real.pi) + 1 / w) / Real.sqrt x ≤ 7 * E := by
  have hp := Real.log_le_sub_one_of_pos (mul_pos (by norm_num only : (0 : ℝ) < 2) Real.pi_pos)
  have hi := (div_le_one (zero_lt_one.trans_le hw)).2 hw
  have hn : Real.log (2 * Real.pi) + 1 / w ≤ 7 := by linarith only [hp, hi, Real.pi_lt_d4]
  calc
    _ ≤ 7 / Real.sqrt x := div_le_div_of_nonneg_right hn hx.le
    _ ≤ _ := by
      simpa only [mul_one_div] using mul_le_mul_of_nonneg_left he (by norm_num only : (0 : ℝ) ≤ 7)

/-- A single exponential certificate covers the constant terms throughout the phase band. -/
private theorem band_constants_le {L : ℝ} (hl : 22 ≤ L) :
    let x := Real.exp L
    let a := x - x * (L / Real.exp (L / 2) / 4)
    (Real.log (2 * Real.pi) + 1 / (x - a)) / Real.sqrt x ≤ 7 / 50000 := by
  extract_lets  x a
  have hs : Real.sqrt x = Real.exp (L / 2) := by
    dsimp only [x]
    rw [Real.sqrt_eq_rpow, ← Real.exp_mul]
    congr 1
    ring
  have hp : 0 < Real.sqrt x := hs.symm ▸ Real.exp_pos _
  have h :=
    decay_tick 11 (1 / 50000) (by decide +kernel) (by decide +kernel)
      (show ((11 : ℚ) : ℝ) ≤ L / 2 by
        norm_num only [Rat.cast_ofNat]; linarith only [hl])
      (by decide +kernel)
  rw [Real.exp_neg, ← one_div, ← hs] at h
  norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at h
  have hm := (div_le_div_iff₀ hp (show (0 : ℝ) < 50000 by norm_num only)).1 h
  have hw := (div_eq_iff hp.ne').mp (half_width_eq L)
  change (x - a) / 2 = L / 8 * Real.sqrt x at hw
  have hw1 : 1 ≤ x - a := by nlinarith only [hw, mul_nonneg (sub_nonneg.mpr hl) hp.le, hm]
  simpa only [mul_one_div] using smooth_constants_le hw1 hp h

/-- Normalize the curvature term using the relative smoothing width. -/
private theorem curvature_bound {a x d : ℝ} (ha : 0 < a) (hax : a ≤ x) (hd : 0 ≤ d)
    (hw : x - a ≤ a * d) :
    (3640 * a ^ (-(3 / 2 : ℝ)) * (x - a) ^ 2 / 24) / Real.sqrt x ≤ 3640 * d ^ 2 / 24 := by
  have hp : a ^ (-(3 / 2 : ℝ)) = Real.sqrt a / a ^ 2 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast a 2, ← Real.rpow_sub ha]
    congr 1
    norm_num only
  have hs := Real.sqrt_le_sqrt hax
  have hw2 := sq_le_sq' (by linarith only [hax, mul_nonneg ha.le hd] : -(a * d) ≤ x - a) hw
  have hm := mul_le_mul hw2 hs (Real.sqrt_nonneg a) (sq_nonneg _)
  rw [hp]
  apply (div_le_iff₀ (Real.sqrt_pos.2 (ha.trans_le hax))).2
  field_simp [ha.ne']
  nlinarith only [hm]

/-- Bound the curvature uniformly when the interval spans at most one thousandth of x. -/
theorem small_width_curvature {x u : ℝ} (hx : 0 < x) (hu : 0 ≤ u) (hc : u ≤ 1 / 1000) :
    let a := x - x * u
    (3640 * a ^ (-(3 / 2 : ℝ)) * (x - a) ^ 2 / 24) / Real.sqrt x ≤ 3640 * (1 / 999) ^ 2 / 24 := by
  have hm := mul_le_mul_of_nonneg_left hc hx.le
  have hp : 0 < x - x * u := by linarith only [hm, hx]
  apply curvature_bound hp (sub_le_self _ (mul_nonneg hx.le hu)) (by norm_num only)
  linarith only [hm]

/-- The normalized midpoint factor is in the unit interval, including for signed phase caps. -/
private theorem midpoint_phase_cap {x a k : ℝ} (hx : 0 < x) (ha : a ≤ x) :
    Real.sqrt ((a + x) / 2) * k / Real.sqrt x ≤ max 0 k := by
  apply (div_le_iff₀ (Real.sqrt_pos.2 hx)).2
  rw [mul_comm (max 0 k)]
  calc
    _ ≤ Real.sqrt ((a + x) / 2) * max 0 k :=
      mul_le_mul_of_nonneg_left (le_max_right _ _) (Real.sqrt_nonneg _)
    _ ≤ _ :=
      mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (by linarith only [ha])) (le_max_left _ _)

/-- A signed midpoint cap gives the normalized lower theta error on a closed phase cell.
The endpoint logarithm, curvature and constant terms are bounded uniformly.
Only the midpoint cap and the prime-power correction vary between cells. -/
theorem theta_phase_error {l b L K D : ℝ} (hRH : RiemannHypothesis) (hl : 22 ≤ l) (hb : b ≤ 27)
    (hL : L ∈ Set.Icc l b)
    (hm :
      let x := Real.exp L
          let a := x - x * (L / Real.exp (L / 2) / 4)
          lowerMidpointSum ((a + x) / 2) ≤ Real.sqrt ((a + x) / 2) * K)
    (hd :
      1 + 4 / 5 * Real.exp (-L / 4) + Real.exp (-L / 6) + 81 / 100 * Real.exp (-L / 3) +
          Real.exp (-3 * L / 10) +
          81 / 100 * Real.exp (-2 * L / 5) ≤
        D) :
    let c := b / 2 - (0.6931471803 + 2 * 1.0986122885 + 1 - 18 / (l * (6283 / 8000)))
    (Real.exp L - Chebyshev.theta (Real.exp L)) / Real.sqrt (Real.exp L) ≤
      b / 8 + 7 / 50000 + max 0 K + 3640 * (1 / 999) ^ 2 / 24 +
        ((c ^ 2 + 2 * c + 2) / (6283 / 1000) - 143 / 125) +
        D := by
  let x := Real.exp L
  let u := L / Real.exp (L / 2) / 4
  let a := x - x * u
  have h22 := hl.trans hL.1
  have hx := Real.exp_pos L
  have hu : 0 < u := div_pos (div_pos (by linarith only [h22]) (Real.exp_pos _)) (by norm_num only)
  have cap := cap_of_ticks 22 (1 / 1000) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at cap
  have hs : u ≤ 1 / 1000 :=
    (div_le_div_of_nonneg_right (ratio_le_left (by norm_num only : (2 : ℝ) ≤ 22) h22)
          (by norm_num only : (0 : ℝ) ≤ 4)).trans
      cap
  have ha : 1 < a := by
    have hx3 : 3 ≤ x := by linarith only [Real.add_one_le_exp L, h22]
    have hp := mul_le_mul_of_nonneg_left hs hx.le
    dsimp only [a]
    linarith only [hx3, hp]
  have hax : a < x := sub_lt_self _ (mul_pos hx hu)
  have ht : 100 ≤ 2 / u := (le_div_iff₀ hu).2 (by linarith only [hs])
  have hp :=
    psi_lower_of_midpoint hRH ha hax hu
      (by
        dsimp only [a]; ring)
      ht hm
  have htheta := Arithmetic.theta_lower_of_psi_phase h22 (hL.2.trans hb) hp hd
  have hv :=
    Real.log_nonneg
      ((one_le_div (mul_pos (by norm_num only) Real.pi_pos)).2
        (by linarith only [ht, Real.pi_lt_d4] : 2 * Real.pi ≤ 2 / u))
  have htail :=
    tail_of_cutoff_cap (by linarith only [ht] : 1 ≤ 2 / u) hv
      (cell_cutoff_cap (by linarith only [hl]) hL.1 hL.2)
  have hw := half_width_eq L
  have hc := band_constants_le h22
  have hk := small_width_curvature hx hu.le hs
  have hmid := midpoint_phase_cap (k := K) hx hax.le
  dsimp only [a, x, u] at htheta htail hw hc hk hmid ⊢
  simp only [add_div] at htheta htail hc hmid ⊢
  linarith only [htheta, htail, hw, hc, hk, hmid, hL.2]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
