/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterVariation570
import PseudoPrime.Analysis.LogTaylorBounds

/-! # Inner variation of the section 31 density -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- At every radius at least 278 both critical coordinates occur on the integration
interval from one to the square radius, in decreasing order of coordinate. -/
theorem quarter_inner_roots_570 {r : ℝ} (hr : 278 ≤ r) :
    let X := r ^ 2
    ∃ a b : ℝ,
      1 ≤ a ∧
        a ≤ b ∧
        b ≤ X ∧
        quarterCoord570 X a = 51 / 26 * (5 + Real.sqrt 5) ∧
        quarterCoord570 X b = 51 / 26 * (5 - Real.sqrt 5) := by
  intro X
  have hx : (77284 : ℝ) ≤ X :=
    (by norm_num only : (77284 : ℝ) = 278 ^ 2) ▸ pow_le_pow_left₀ (by norm_num only) hr 2
  have hx1 : 1 ≤ X := by linarith only [hx]
  have hx0 := zero_lt_one.trans_le hx1
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound (N := 77284) (j := 16) (n := 32) (lo := 56 / 5) (hi :=
        12) (by decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlog
  have hL := hlog.trans (Real.log_le_log (by norm_num only) hx)
  have hv1 : (142 / 10 : ℝ) ≤ quarterCoord570 X 1 := by
    unfold quarterCoord570
    rw [one_div, Real.log_inv]
    norm_num only
    linarith only [hL]
  have hvX : quarterCoord570 X X = 357 / 125 := by
    norm_num only [quarterCoord570, div_self hx0.ne', Real.log_one, sub_zero]
  have hs := Real.sq_sqrt (by norm_num only : (0 : ℝ) ≤ 5)
  have hz := Real.sqrt_nonneg (5 : ℝ)
  have hsmall : Real.sqrt 5 ≤ 2237 / 1000 := by nlinarith only [hs, hz]
  have hc : ContinuousOn (quarterCoord570 X) (Set.Icc 1 X) := by
    intro t ht
    apply ContinuousAt.continuousWithinAt
    have hpos := zero_lt_one.trans_le ht.1
    unfold quarterCoord570
    fun_prop (disch := positivity)
  obtain ⟨a, ha, hA⟩ :=
    intermediate_value_Icc' hx1 hc
      (show 51 / 26 * (5 + Real.sqrt 5) ∈ Set.Icc (quarterCoord570 X X) (quarterCoord570 X 1) from
        ⟨by linarith only [hvX, hz], by linarith only [hv1, hsmall]⟩)
  obtain ⟨b, hb, hB⟩ :=
    intermediate_value_Icc' ha.2 (hc.mono (Set.Icc_subset_Icc_left ha.1))
      (show 51 / 26 * (5 - Real.sqrt 5) ∈ Set.Icc (quarterCoord570 X X) (quarterCoord570 X a) from
        ⟨by linarith only [hvX, hsmall], by linarith only [hA, hz]⟩)
  exact ⟨a, b, ha.1, hb.1, hb.2, hA, hB⟩

private theorem primitive_nonneg {X t : ℝ} (hv : 14 ≤ quarterCoord570 X t) :
    0 ≤ quarterSqrtPrimitive570 X t := by
  let w := quarterCoord570 X t - 14
  have hw : 0 ≤ w := sub_nonneg.mpr hv
  have he : quarterCoord570 X t = w + 14 := by
    dsimp only [w]; ring
  unfold quarterSqrtPrimitive570
  rw [he]
  norm_num only [Analysis.logPowerTailPoly]
  have h :
    0 ≤
      Real.exp (-1 * (w + 14)) *
        (3349243 / 38250 +
          w *
            (16599 / 170 +
              w *
                (374653 / 15300 + w * (39209 / 15300 + w * (52 / 425 + w * (169 / 76500)))))) := by
    positivity
  convert h using 1; ring

private theorem cutoff_primitive_upper {X : ℝ} (hx : 0 < X) :
    quarterSqrtPrimitive570 X X < 672 / 10000 := by
  have hv : quarterCoord570 X X = 357 / 125 := by
    norm_num only [quarterCoord570, div_self hx.ne', Real.log_one, sub_zero]
  have h := Real.sum_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 357 / 125) 18
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one] at h
  have he := one_div_le_one_div_of_le (by norm_num only) h
  rw [one_div (Real.exp _), ← Real.exp_neg] at he
  norm_num only [quarterSqrtPrimitive570, hv, Analysis.logPowerTailPoly]
  linarith only [he]

/-- For r at least 278 the inner sqrt-weighted absolute variation is below 0.11935.
The middle negative arc contributes twice its absolute mass to the signed endpoint difference. -/
theorem quarter_inner_variation_570 {r : ℝ} (hr : 278 ≤ r) :
    let X := r ^ 2
    let Q := deriv (fun u ↦ u * deriv (quarterWeight570 X) u)
    (∫ t in (1 : ℝ)..X, Real.sqrt t * |Q t|) < 11935 / 100000 := by
  intro X Q
  obtain ⟨a, b, ha, hab, hb, hA, hB⟩ := quarter_inner_roots_570 hr
  have hx1 := ha.trans (hab.trans hb)
  have hx : 0 < X := zero_lt_one.trans_le hx1
  have ha0 := zero_lt_one.trans_le ha
  have hb0 := ha0.trans_le hab
  have hmono {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) : quarterCoord570 X v ≤ quarterCoord570 X u := by
    have h := Real.log_le_log (div_pos hu hx) (div_le_div_of_nonneg_right huv hx.le)
    unfold quarterCoord570
    norm_num only
    linarith only [h]
  have hvX : quarterCoord570 X X = 357 / 125 := by
    norm_num only [quarterCoord570, div_self hx.ne', Real.log_one, sub_zero]
  have hs := Real.sq_sqrt (by norm_num only : (0 : ℝ) ≤ 5)
  have hz := Real.sqrt_nonneg (5 : ℝ)
  have hslo : (22 / 10 : ℝ) ≤ Real.sqrt 5 := by nlinarith only [hs, hz]
  have hv1 := hmono zero_lt_one ha
  have hstart := primitive_nonneg (by linarith only [hv1, hA, hslo] : 14 ≤ quarterCoord570 X 1)
  have hpos {t : ℝ} (ht : 0 < t) (htX : t ≤ X) (hside : t ≤ a ∨ b ≤ t) : 0 ≤ Q t := by
    have hv := hmono ht htX
    have htcoord : 0 ≤ quarterCoord570 X t := by linarith only [hvX, hv]
    have hf : 0 ≤ quarterFactor570 X t := by
      unfold quarterFactor570; positivity
    rw [show Q t = _ from quarter_density_roots_570 hx ht, mul_assoc]
    apply
      mul_nonneg
        (by positivity : 0 ≤ quarterFactor570 X t / t * quarterCoord570 X t ^ 3 * (13 / 25) ^ 2) _
    rcases hside with hl | hu
    · have h := hmono ht hl
      exact mul_nonneg (by linarith only [h, hA, hz]) (by linarith only [h, hA])
    · have h := hmono hb0 hu
      exact mul_nonneg_of_nonpos_of_nonpos (by linarith only [h, hB]) (by linarith only [h, hB, hz])
  have hpiece {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) (h : ∀ t ∈ Set.Icc u v, 0 ≤ Q t) :
    (∫ t in u..v, Real.sqrt t * |Q t|) =
      quarterSqrtPrimitive570 X v - quarterSqrtPrimitive570 X u := by
    rw [← quarter_sqrt_moment_570 hx hu huv]
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [abs_of_nonneg (h t (Set.uIcc_of_le huv ▸ ht))]
  have hl :=
    hpiece zero_lt_one ha
      (fun t ht ↦ hpos (zero_lt_one.trans_le ht.1) (ht.2.trans (hab.trans hb)) (Or.inl ht.2))
  have hh := hpiece hb0 hb (fun t ht ↦ hpos (hb0.trans_le ht.1) ht.2 (Or.inr ht.1))
  have hi {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    IntervalIntegrable (fun t ↦ Real.sqrt t * |Q t|) MeasureTheory.volume u v := by
    apply ContinuousOn.intervalIntegrable
    apply Real.continuous_sqrt.continuousOn.mul
    apply ContinuousOn.abs
    intro t ht
    have hp := hu.trans_le ((Set.uIcc_of_le huv ▸ ht : t ∈ Set.Icc u v).1)
    apply ContinuousAt.continuousWithinAt
    have he :=
      Filter.eventually_of_mem (isOpen_Ioi.mem_nhds hp : Set.Ioi (0 : ℝ) ∈ nhds t)
        (fun y hy ↦ quarter_second_density_570 (t := y) hx hy)
    apply ContinuousAt.congr _ (Filter.EventuallyEq.symm he)
    unfold quarterFactor570 quarterCoord570
    fun_prop (disch := positivity)
  have hm := quarter_middle_variation_570 hx ha0 hab hA hB
  rw [←
    intervalIntegral.integral_add_adjacent_intervals (hi zero_lt_one (ha.trans hab)) (hi hb0 hb), ←
    intervalIntegral.integral_add_adjacent_intervals (hi zero_lt_one ha) (hi ha0 hab), hl, hh]
  dsimp only [Q] at *
  linarith only [hm, hstart, cutoff_primitive_upper hx, (quarter_root_upper_value hA).2,
    (quarter_root_lower_value hB).1]

end PseudoPrime.PrimeTestBounds.MillerRabin
