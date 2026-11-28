/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterInner570
import PseudoPrime.Analysis.ExponentialFixedPointBounds
import Mathlib.Analysis.SpecialFunctions.Sqrt
import PseudoPrime.LLS.ClippedLogShiftPrincipalBounds

/-! # Unweighted variation for the section 31 principal density -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private theorem lower_root_sqrt {X b : ℝ} (hx : 77284 ≤ X) (hb : 0 < b)
    (hv : quarterCoord570 X b = 51 / 26 * (5 - Real.sqrt 5)) : 60 ≤ Real.sqrt b := by
  have hx0 : 0 < X := by linarith only [hx]
  have hs := Real.sq_sqrt (by norm_num only : (0 : ℝ) ≤ 5)
  have hz := Real.sqrt_nonneg (5 : ℝ)
  have hl : (22 / 10 : ℝ) ≤ Real.sqrt 5 := by nlinarith only [hs, hz]
  unfold quarterCoord570 at hv
  norm_num only at hv
  have hlog : -3 ≤ Real.log (b / X) := by linarith only [hv, hl]
  have he :=
    Analysis.exp_le_taylor_add_two_next (x := (3 : ℝ)) (n := 16) (by norm_num only)
      (by norm_num only)
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one] at he
  have hi := one_div_le_one_div_of_le (Real.exp_pos _) (by linarith only [he] : Real.exp 3 ≤ 21)
  rw [one_div (Real.exp _), ← Real.exp_neg] at hi
  have h := hi.trans ((Real.exp_le_exp.mpr hlog).trans_eq (Real.exp_log (div_pos hb hx0)))
  apply Real.le_sqrt_of_sq_le
  linarith only [(le_div_iff₀ hx0).mp h, hx]

private theorem scaled_log_deriv {X t : ℝ} (hx : 0 < X) (ht : 0 < t) :
    let v := quarterCoord570 X t
    (t * deriv (quarterWeight570 X) t) * Real.sqrt t * Real.exp v =
      v ^ 4 * ((13 / 25) * v - 51 / 10) / 120 := by
  intro v
  rw [quarter_log_deriv_570 hx ht]
  dsimp only [quarterFactor570, v]
  rw [Real.exp_neg]
  field_simp [(Real.sqrt_pos.mpr ht).ne', (Real.exp_pos _).ne']
  ring

/-- At the larger critical coordinate the logarithmic weight derivative is less
than 0.0007 when the integration variable is at least one. -/
theorem quarter_upper_root_deriv {X t : ℝ} (hx : 0 < X) (ht : 1 ≤ t)
    (hv : quarterCoord570 X t = 51 / 26 * (5 + Real.sqrt 5)) :
    t * deriv (quarterWeight570 X) t < 7 / 10000 := by
  let v := quarterCoord570 X t
  have hs := Real.sq_sqrt (by norm_num only : (0 : ℝ) ≤ 5)
  have hz := Real.sqrt_nonneg (5 : ℝ)
  have hl : (22 / 10 : ℝ) ≤ Real.sqrt 5 := by nlinarith only [hs, hz]
  have hu : Real.sqrt 5 ≤ 2237 / 1000 := by nlinarith only [hs, hz]
  have h1 : 14 ≤ v := by
    dsimp only [v]; linarith only [hv, hl]
  have h2 : v ≤ 142 / 10 := by
    dsimp only [v]; linarith only [hv, hu]
  have he := Real.sum_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 14) 39
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one] at he
  have hev := (by linarith only [he] : (1200000 : ℝ) ≤ Real.exp 14).trans (Real.exp_le_exp.mpr h1)
  have hden :=
    mul_le_mul (Real.le_sqrt_of_sq_le (by linarith only [ht] : (1 : ℝ) ^ 2 ≤ t)) hev
      (by norm_num only) (Real.sqrt_nonneg _)
  have hnum :=
    mul_le_mul (pow_le_pow_left₀ (by linarith only [h1]) h2 4)
      (by linarith only [h2] : 13 / 25 * v - 51 / 10 ≤ 23 / 10) (by linarith only [h1])
      (by norm_num only)
  have ht0 := zero_lt_one.trans_le ht
  have hd := scaled_log_deriv hx ht0
  change _ * _ * Real.exp v = v ^ 4 * _ / 120 at hd
  apply (mul_lt_mul_iff_left₀ (mul_pos (Real.sqrt_pos.mpr ht0) (Real.exp_pos v))).mp
  linarith only [hd, hnum, hden]

/-- At the smaller critical coordinate the logarithmic derivative exceeds
-0.0014 for every square cutoff at least 77284. -/
theorem quarter_lower_root_deriv {X t : ℝ} (hx : 77284 ≤ X) (ht : 0 < t)
    (hv : quarterCoord570 X t = 51 / 26 * (5 - Real.sqrt 5)) :
    -(14 / 10000) < t * deriv (quarterWeight570 X) t := by
  let v := quarterCoord570 X t
  have hs := Real.sq_sqrt (by norm_num only : (0 : ℝ) ≤ 5)
  have hz := Real.sqrt_nonneg (5 : ℝ)
  have hl : (223 / 100 : ℝ) ≤ Real.sqrt 5 := by nlinarith only [hs, hz]
  have hu : Real.sqrt 5 ≤ 224 / 100 := by nlinarith only [hs, hz]
  have h1 : 54 / 10 ≤ v := by
    dsimp only [v]; linarith only [hv, hu]
  have h2 : v ≤ 545 / 100 := by
    dsimp only [v]; linarith only [hv, hl]
  have he := Real.sum_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 54 / 10) 24
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one] at he
  norm_num only at h1
  have hev := (by linarith only [he] : (220 : ℝ) ≤ Real.exp (27 / 5)).trans (Real.exp_le_exp.mpr h1)
  have hden := mul_le_mul (lower_root_sqrt hx ht hv) hev (by norm_num only) (Real.sqrt_nonneg _)
  have hnum :=
    mul_le_mul (pow_le_pow_left₀ (by linarith only [h1]) h2 4)
      (by linarith only [h1] : 51 / 10 - 13 / 25 * v ≤ 23 / 10) (by linarith only [h2])
      (by norm_num only)
  have hd := scaled_log_deriv (by linarith only [hx] : 0 < X) ht
  change _ * _ * Real.exp v = v ^ 4 * _ / 120 at hd
  apply (mul_lt_mul_iff_left₀ (mul_pos (Real.sqrt_pos.mpr ht) (Real.exp_pos v))).mp
  linarith only [hd, hnum, hden]

/-- The three sign intervals give unweighted absolute variation below 0.0042. -/
theorem quarter_inner_plain_variation_570 {r : ℝ} (hr : 278 ≤ r) :
    let X := r ^ 2
    let Q := deriv (fun u ↦ u * deriv (quarterWeight570 X) u)
    (∫ t in (1 : ℝ)..X, |Q t|) < 42 / 10000 := by
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
  let P := fun t ↦ t * deriv (quarterWeight570 X) t
  have hstart : 0 ≤ P 1 := by
    rw [show P 1 = _ from quarter_log_deriv_570 hx zero_lt_one]
    have hf : 0 ≤ quarterFactor570 X 1 := by
      unfold quarterFactor570; positivity
    apply mul_nonneg hf
    have h :=
      mul_nonneg (pow_nonneg (by linarith only [hv1, hA, hslo] : 0 ≤ quarterCoord570 X 1) 4)
        (by linarith only [hv1, hA, hslo] : 0 ≤ 13 / 25 * quarterCoord570 X 1 - 51 / 10)
    linarith only [h]
  have hend : P X ≤ 0 := by
    rw [show P X = _ from quarter_log_deriv_570 hx hx, hvX]
    apply
      mul_nonpos_of_nonneg_of_nonpos
        (by
          unfold quarterFactor570; positivity)
    norm_num only
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
  have hcont {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) : ContinuousOn Q (Set.uIcc u v) := by
    intro t ht
    have hp := hu.trans_le ((Set.uIcc_of_le huv ▸ ht : t ∈ Set.Icc u v).1)
    apply ContinuousAt.continuousWithinAt
    have he :=
      Filter.eventually_of_mem (isOpen_Ioi.mem_nhds hp : Set.Ioi (0 : ℝ) ∈ nhds t)
        (fun y hy ↦ quarter_second_density_570 (t := y) hx hy)
    apply ContinuousAt.congr _ (Filter.EventuallyEq.symm he)
    unfold quarterFactor570 quarterCoord570
    fun_prop (disch := positivity)
  have hi {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    IntervalIntegrable (fun t ↦ |Q t|) MeasureTheory.volume u v :=
    (hcont hu huv).abs.intervalIntegrable
  have hint {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) : (∫ t in u..v, Q t) = P v - P u := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ (hcont hu huv).intervalIntegrable
    intro t ht
    have ht0 := hu.trans_le ((Set.uIcc_of_le huv ▸ ht : t ∈ Set.Icc u v).1)
    have he :=
      Filter.eventually_of_mem (isOpen_Ioi.mem_nhds ht0 : Set.Ioi (0 : ℝ) ∈ nhds t)
        (fun y hy ↦ quarter_log_deriv_570 (t := y) hx hy)
    apply DifferentiableAt.hasDerivAt
    apply DifferentiableAt.congr_of_eventuallyEq _ he
    unfold quarterFactor570 quarterCoord570
    fun_prop (disch := positivity)
  have hpiece {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) (h : ∀ t ∈ Set.Icc u v, 0 ≤ Q t) :
    (∫ t in u..v, |Q t|) = P v - P u := by
    rw [← hint hu huv]
    apply intervalIntegral.integral_congr
    intro t ht
    exact abs_of_nonneg (h t (Set.uIcc_of_le huv ▸ ht))
  have hl :=
    hpiece zero_lt_one ha
      (fun t ht ↦ hpos (zero_lt_one.trans_le ht.1) (ht.2.trans (hab.trans hb)) (Or.inl ht.2))
  have hh := hpiece hb0 hb (fun t ht ↦ hpos (hb0.trans_le ht.1) ht.2 (Or.inr ht.1))
  have hm : (∫ t in a..b, |Q t|) = -(P b - P a) := by
    rw [← hint ha0 hab, ← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    have ht0 := ha0.trans_le ht.1
    have h1 := hmono ht0 ht.2
    have h2 := hmono ha0 ht.1
    exact
      abs_of_nonpos
        ((quarter_density_nonpos_iff hx ht0 (by linarith only [hvX, hmono ht0 (ht.2.trans hb)])).mpr
          ⟨hB ▸ h1, hA ▸ h2⟩)
  rw [←
    intervalIntegral.integral_add_adjacent_intervals (hi zero_lt_one (ha.trans hab)) (hi hb0 hb), ←
    intervalIntegral.integral_add_adjacent_intervals (hi zero_lt_one ha) (hi ha0 hab), hl, hh, hm]
  have hx' : 77284 ≤ X :=
    (by norm_num only : (77284 : ℝ) = 278 ^ 2) ▸ pow_le_pow_left₀ (by norm_num only) hr 2
  dsimp only [P] at *
  linarith only [hstart, hend, quarter_upper_root_deriv hx ha hA,
    quarter_lower_root_deriv hx' hb0 hB]

/-- RH bounds the inner centered integral below by -0.010378.
Apply the square-root and constant parts of the arithmetic envelope separately. -/
theorem quarter_inner_error_570 {r : ℝ} (hr : 278 ≤ r) (hRH : RiemannHypothesis) :
    let X := r ^ 2
    let Q := deriv (fun u ↦ u * deriv (quarterWeight570 X) u)
    let E := fun t ↦
      AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t -
        (t - Real.log (2 * Real.pi) * Real.log t)
    show Prop from -(10378 / 1000000) < (∫ t in (1 : ℝ)..X, E t * Q t) := by
  intro X Q E
  have hx1 : 1 ≤ X :=
    (by norm_num only : (1 : ℝ) ≤ 278 ^ 2).trans (pow_le_pow_left₀ (by norm_num only) hr 2)
  have hx := zero_lt_one.trans_le hx1
  have hq : ContinuousOn Q (Set.uIcc 1 X) := by
    intro t ht
    have hp := zero_lt_one.trans_le ((Set.uIcc_of_le hx1 ▸ ht : t ∈ Set.Icc 1 X).1)
    apply ContinuousAt.continuousWithinAt
    have he :=
      Filter.eventually_of_mem (isOpen_Ioi.mem_nhds hp : Set.Ioi (0 : ℝ) ∈ nhds t)
        (fun y hy ↦ quarter_second_density_570 (t := y) hx hy)
    apply ContinuousAt.congr _ (Filter.EventuallyEq.symm he)
    unfold quarterFactor570 quarterCoord570
    fun_prop (disch := positivity)
  have heq {t : ℝ} (ht : 1 ≤ t) : LLS.clippedShiftError 1 t = E t := by
    simp only [LLS.clippedShiftError, E, one_mul, div_one, Analysis.positiveLogRatio_eq_log ht]
    ring
  have hc :=
    (LLS.clippedShiftError_continuousOn (x := 1) zero_lt_one X).mono
      (Set.Icc_subset_Icc_left zero_le_one)
  have hi := (hc.congr (fun t ht ↦ (heq ht.1).symm)).mul (Set.uIcc_of_le hx1 ▸ hq)
  rw [← Set.uIcc_of_le hx1] at hi
  have ha :=
    (Real.continuous_sqrt.continuousOn.mul hq.abs).intervalIntegrable (μ := MeasureTheory.volume)
  have hb := hq.abs.intervalIntegrable (μ := MeasureTheory.volume)
  have h :=
    intervalIntegral.integral_mono_on hx1
      ((ha.const_mul (-(1 / 20 : ℝ))).sub (hb.const_mul (21 / 20))) hi.intervalIntegrable
      (fun t ht ↦
        show -(1 / 20) * (Real.sqrt t * |Q t|) - 21 / 20 * |Q t| ≤ E t * Q t
          by
          have he := LLS.clippedShiftError_abs_le hRH zero_lt_one (zero_le_one.trans ht.1)
          rw [one_mul, heq ht.1] at he
          have hz := mul_le_mul_of_nonneg_right he (abs_nonneg (Q t))
          have hd := neg_abs_le (E t * Q t)
          rw [abs_mul] at hd
          linarith only [hz, hd])
  rw [intervalIntegral.integral_sub (ha.const_mul _) (hb.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at h
  dsimp only [X, Q] at *
  simp only [Pi.mul_apply] at h
  linarith only [h, quarter_inner_variation_570 hr, quarter_inner_plain_variation_570 hr]

/-- The centered integrals and the cutoff residual together cost less than 0.065746
in the principal difference for every radius at least 278 under RH. -/
theorem quarter_principal_integrals_570 {r : ℝ} (hr : 278 ≤ r) (hRH : RiemannHypothesis) :
    let X := r ^ 2
    let B := X * Real.exp (14 / 5)
    let W := quarterWeight570 X
    let S := fun n : ℕ ↦ (quarterKernel570.summand (1 : DirichletCharacter ℂ 1) X n).re
    let c := Real.log (2 * Real.pi)
    4 * (∫ t in (1 : ℝ)..X, W t) - (∫ t in (1 : ℝ)..B, W t) + 4 * W X * (Chebyshev.psi X - X + c) -
            3 * deriv W 1 +
          3 * (1 - c) * W 1 -
        65746 / 1000000 <
      4 * (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, S n) - (∑' n : ℕ, S n) := by
  intro X B W S c
  have h := quarter_inner_lower_570 hr hRH
  have he := quarter_inner_error_570 hr hRH
  dsimp only [X, B, W, S, c] at *
  linarith only [h, he]

end PseudoPrime.PrimeTestBounds.MillerRabin
