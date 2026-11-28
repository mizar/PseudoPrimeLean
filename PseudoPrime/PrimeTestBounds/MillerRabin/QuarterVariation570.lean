/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterDensity570
import PseudoPrime.LLS.ClippedLogShiftPrincipalBounds
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterEndpoint570
import PseudoPrime.Analysis.ExponentialFixedPointBounds

/-! # Values of the section 31 square-root primitive at its turning points -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private theorem primitive_at_root {X t z : ℝ} (hz : z ^ 2 = 5)
    (hv : quarterCoord570 X t = 51 / 26 * (5 + z)) :
    quarterSqrtPrimitive570 X t =
      (1750763 / 34476 + 42811 / 1690 * z) * Real.exp (-(quarterCoord570 X t)) := by
  unfold quarterSqrtPrimitive570
  rw [hv]
  norm_num only [Analysis.logPowerTailPoly, neg_one_mul]
  ring_nf
  rw [show z ^ 5 = z ^ 2 * z ^ 2 * z by ring, show z ^ 4 = z ^ 2 * z ^ 2 by ring,
    show z ^ 3 = z ^ 2 * z by ring, hz]
  ring

/-- The square-root primitive at the smaller critical coordinate lies between
these rational endpoints. -/
theorem quarter_root_lower_value {X t : ℝ}
    (hv : quarterCoord570 X t = 51 / 26 * (5 - Real.sqrt 5)) :
    (-260 / 10000 : ℝ) < quarterSqrtPrimitive570 X t ∧
      quarterSqrtPrimitive570 X t < -258 / 10000 := by
  let v := quarterCoord570 X t
  let p := (1750763 / 34476 : ℝ) + 42811 / 1690 * (-Real.sqrt 5)
  have hs := Real.sq_sqrt (by norm_num only : (0 : ℝ) ≤ 5)
  have hz := Real.sqrt_nonneg (5 : ℝ)
  have h1 : (2236067 / 1000000 : ℝ) ≤ Real.sqrt 5 := by nlinarith only [hs, hz]
  have h2 : Real.sqrt 5 ≤ (2236068 / 1000000 : ℝ) := by nlinarith only [hs, hz]
  have hvl : (5421 / 1000 : ℝ) ≤ v := by
    dsimp only [v]; linarith only [hv, h1, h2]
  have hvu : v ≤ (5422 / 1000 : ℝ) := by
    dsimp only [v]; linarith only [hv, h1, h2]
  have hpl : (-587 / 100 : ℝ) ≤ p := by
    dsimp only [p]; linarith only [h1, h2]
  have hpu : p ≤ (-585 / 100 : ℝ) := by
    dsimp only [p]; linarith only [h1, h2]
  have hl := Real.sum_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 5421 / 1000) 46
  have hu :=
    Analysis.exp_le_taylor_add_two_next (x := (5422 / 1000 : ℝ)) (n := 48) (by norm_num only)
      (by norm_num only)
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one] at hl hu
  norm_num only at hvu
  have he1 := hl.trans (Real.exp_le_exp.mpr hvl)
  have he2 := (Real.exp_le_exp.mpr hvu).trans hu
  rw [primitive_at_root (z := -Real.sqrt 5) (by nlinarith only [hs]) (by linarith only [hv]),
    Real.exp_neg, ← div_eq_mul_inv]
  change _ < p / Real.exp v ∧ p / Real.exp v < _
  rw [lt_div_iff₀ (Real.exp_pos _), div_lt_iff₀ (Real.exp_pos _)]
  constructor <;> linarith only [he1, he2, hpl, hpu]

/-- The square-root primitive at the larger critical coordinate lies between
these rational endpoints. -/
theorem quarter_root_upper_value {X t : ℝ}
    (hv : quarterCoord570 X t = 51 / 26 * (5 + Real.sqrt 5)) :
    (735 / 10000000 : ℝ) < quarterSqrtPrimitive570 X t ∧
      quarterSqrtPrimitive570 X t < 737 / 10000000 := by
  let v := quarterCoord570 X t
  let p := (1750763 / 34476 : ℝ) + 42811 / 1690 * (Real.sqrt 5)
  have hs := Real.sq_sqrt (by norm_num only : (0 : ℝ) ≤ 5)
  have hz := Real.sqrt_nonneg (5 : ℝ)
  have h1 : (2236067 / 1000000 : ℝ) ≤ Real.sqrt 5 := by nlinarith only [hs, hz]
  have h2 : Real.sqrt 5 ≤ (2236068 / 1000000 : ℝ) := by nlinarith only [hs, hz]
  have hvl : (14193 / 1000 : ℝ) ≤ v := by
    dsimp only [v]; linarith only [hv, h1, h2]
  have hvu : v ≤ (14194 / 1000 : ℝ) := by
    dsimp only [v]; linarith only [hv, h1, h2]
  have hpl : (10742 / 100 : ℝ) ≤ p := by
    dsimp only [p]; linarith only [h1, h2]
  have hpu : p ≤ (10744 / 100 : ℝ) := by
    dsimp only [p]; linarith only [h1, h2]
  have hl := Real.sum_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 14193 / 1000) 46
  have hu :=
    Analysis.exp_le_taylor_add_two_next (x := (14194 / 1000 : ℝ)) (n := 48) (by norm_num only)
      (by norm_num only)
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one] at hl hu
  norm_num only at hvu
  have he1 := hl.trans (Real.exp_le_exp.mpr hvl)
  have he2 := (Real.exp_le_exp.mpr hvu).trans hu
  rw [primitive_at_root (z := Real.sqrt 5) (by nlinarith only [hs]) (by linarith only [hv]),
    Real.exp_neg, ← div_eq_mul_inv]
  change _ < p / Real.exp v ∧ p / Real.exp v < _
  rw [lt_div_iff₀ (Real.exp_pos _), div_lt_iff₀ (Real.exp_pos _)]
  constructor <;> linarith only [he1, he2, hpl, hpu]

/-- Between the two critical points, the entire square-root-weighted absolute
variation of the section 31 density is less than 0.026074. -/
theorem quarter_middle_variation_570 {X a b : ℝ} (hx : 0 < X) (ha : 0 < a) (hab : a ≤ b)
    (hA : quarterCoord570 X a = 51 / 26 * (5 + Real.sqrt 5))
    (hB : quarterCoord570 X b = 51 / 26 * (5 - Real.sqrt 5)) :
    (∫ t in a..b, Real.sqrt t * |deriv (fun u ↦ u * deriv (quarterWeight570 X) u) t|) <
      26074 / 1000000 := by
  have hmono {x y : ℝ} (hp : 0 < x) (hxy : x ≤ y) : quarterCoord570 X y ≤ quarterCoord570 X x := by
    have h := Real.log_le_log (div_pos hp hx) (div_le_div_of_nonneg_right hxy hx.le)
    unfold quarterCoord570
    norm_num only
    linarith only [h]
  have hpos : 0 < quarterCoord570 X b := by
    have hs := Real.sq_sqrt (by norm_num only : (0 : ℝ) ≤ 5)
    nlinarith only [hs, hB]
  have he :
    (∫ t in a..b, Real.sqrt t * |deriv (fun u ↦ u * deriv (quarterWeight570 X) u) t|) =
      -(∫ t in a..b, Real.sqrt t * deriv (fun u ↦ u * deriv (quarterWeight570 X) u) t) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    have ht0 := ha.trans_le ht.1
    have hl := hmono ht0 ht.2
    have hu := hmono ha ht.1
    have hn := (quarter_density_nonpos_iff hx ht0 (hpos.trans_le hl)).mpr ⟨hB ▸ hl, hA ▸ hu⟩
    dsimp only
    rw [abs_of_nonpos hn, mul_neg]
  rw [he, quarter_sqrt_moment_570 hx ha hab]
  linarith only [(quarter_root_upper_value hA).2, (quarter_root_lower_value hB).1]

/-- The square-root-weighted density between the arithmetic and support cutoffs
has mass below 0.178. Its sign is positive here, so no critical-point split is needed. -/
theorem quarter_outer_moment_570 {X : ℝ} (hx : 0 < X) :
    (∫ t in X..X * Real.exp (14 / 5),
        Real.sqrt t * deriv (fun u ↦ u * deriv (quarterWeight570 X) u) t) <
      178 / 1000 := by
  have hB := le_mul_of_one_le_right hx.le (Real.one_le_exp (by norm_num only : (0 : ℝ) ≤ 14 / 5))
  rw [quarter_sqrt_moment_570 hx hx hB]
  have hc : quarterCoord570 X X = 357 / 125 := by
    norm_num only [quarterCoord570, div_self hx.ne', Real.log_one, sub_zero]
  have hz : quarterCoord570 X (X * Real.exp (14 / 5)) = 0 := by
    norm_num only [quarterCoord570, mul_div_cancel_left₀ _ hx.ne', Real.log_exp]
  have ha :=
    Analysis.exp_le_taylor_add_two_next (x := (357 / 125 : ℝ)) (n := 24) (by norm_num only)
      (by norm_num only)
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one] at ha
  have hi := one_div_le_one_div_of_le (Real.exp_pos _) ha
  rw [one_div (Real.exp _), ← Real.exp_neg] at hi
  norm_num only [quarterSqrtPrimitive570, hz, hc, Analysis.logPowerTailPoly, Real.exp_zero]
  linarith only [hi]

private theorem centered_integrand_continuous {X a b : ℝ} (hx : 0 < X) (ha : 1 ≤ a) :
    let Q := deriv (fun u ↦ u * deriv (quarterWeight570 X) u)
    let E := fun t ↦
      AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t -
        (t - Real.log (2 * Real.pi) * Real.log t)
    ContinuousOn Q (Set.Icc a b) ∧ ContinuousOn (fun t ↦ E t * Q t) (Set.Icc a b) := by
  intro Q E
  have hq : ContinuousOn Q (Set.Icc a b) := by
    intro t ht
    have ht' := zero_lt_one.trans_le (ha.trans ht.1)
    apply ContinuousAt.continuousWithinAt
    have he :=
      Filter.eventually_of_mem (isOpen_Ioi.mem_nhds ht' : Set.Ioi (0 : ℝ) ∈ nhds t)
        (fun u hu ↦ quarter_second_density_570 (t := u) hx hu)
    apply ContinuousAt.congr _ (Filter.EventuallyEq.symm he)
    unfold quarterFactor570 quarterCoord570
    fun_prop (disch := positivity)
  have heq (t : ℝ) (ht : t ∈ Set.Icc a b) : LLS.clippedShiftError 1 t = E t := by
    simp only [LLS.clippedShiftError, E, one_mul, div_one,
      Analysis.positiveLogRatio_eq_log (ha.trans ht.1)]
    ring
  have hc :=
    (LLS.clippedShiftError_continuousOn (x := 1) zero_lt_one b).mono
      (Set.Icc_subset_Icc_left (zero_le_one.trans ha))
  have hi := (hc.congr (fun t ht ↦ (heq t ht).symm)).mul hq
  exact ⟨hq, hi⟩

/-- Under RH the outer centered-error integral is bounded above by 0.009612
for all radii at least 278. On this interval the density is nonnegative and
the absolute arithmetic error is at most 0.054 times the square root. -/
theorem quarter_outer_error_570 {r : ℝ} (hr : 278 ≤ r) (hRH : RiemannHypothesis) :
    let X := r ^ 2
    let B := X * Real.exp (14 / 5)
    let Q := deriv (fun u ↦ u * deriv (quarterWeight570 X) u)
    let E := fun t ↦
      AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t -
        (t - Real.log (2 * Real.pi) * Real.log t)
    (∫ t in X..B, E t * Q t) < 9612 / 1000000 := by
  intro X B Q E
  have hr0 : 0 < r := by linarith only [hr]
  have hx : 0 < X := sq_pos_of_pos hr0
  have hx1 : 1 ≤ X :=
    (by norm_num only : (1 : ℝ) ≤ 278 ^ 2).trans (pow_le_pow_left₀ (by norm_num only) hr 2)
  have hb : X ≤ B := le_mul_of_one_le_right hx.le (Real.one_le_exp (by norm_num only))
  obtain ⟨hq, hi⟩ := centered_integrand_continuous (b := B) hx hx1
  have hj := (Real.continuous_sqrt.continuousOn.mul hq).const_mul (54 / 1000 : ℝ)
  rw [← Set.uIcc_of_le hb] at hi hj
  have h :=
    intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hb hi.intervalIntegrable
      hj.intervalIntegrable
      (fun t ht ↦
        show E t * Q t ≤ 54 / 1000 * (Real.sqrt t * Q t)
          by
          have ht' := hx.le.trans ht.1
          have he := LLS.clippedShiftError_abs_le hRH zero_lt_one ht'
          simp only [LLS.clippedShiftError, one_mul, div_one,
            Analysis.positiveLogRatio_eq_log (hx1.trans ht.1)] at he
          have hs := Real.sqrt_le_sqrt ht.1
          change Real.sqrt (r ^ 2) ≤ Real.sqrt t at hs
          rw [Real.sqrt_sq hr0.le] at hs
          have hh : E t ≤ 54 / 1000 * Real.sqrt t := by
            dsimp only [E]
            linarith only [(abs_le.mp he).2, hr, hs]
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right hh (quarter_outer_density_nonneg hx ht.1 ht.2))
  change (∫ t in X..B, E t * Q t) ≤ ∫ t in X..B, 54 / 1000 * (Real.sqrt t * Q t) at h
  rw [intervalIntegral.integral_const_mul] at h
  have hm := quarter_outer_moment_570 hx
  dsimp only [Q, B, X] at *
  linarith only [h, hm]

/-- After the outer integral and cutoff error are bounded, the only centered
integral left in the lower bound lies on the inner interval and has coefficient three. -/
theorem quarter_inner_lower_570 {r : ℝ} (hr : 278 ≤ r) (hRH : RiemannHypothesis) :
    let X := r ^ 2
    let B := X * Real.exp (14 / 5)
    let W := quarterWeight570 X
    let P := fun t ↦ t * deriv W t
    let S := fun n : ℕ ↦ (quarterKernel570.summand (1 : DirichletCharacter ℂ 1) X n).re
    let c := Real.log (2 * Real.pi)
    let E := fun t ↦ AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t - (t - c * Real.log t)
    4 * (∫ t in (1 : ℝ)..X, W t) - (∫ t in (1 : ℝ)..B, W t) +
              3 * (∫ t in (1 : ℝ)..X, E t * deriv P t) +
              4 * W X * (Chebyshev.psi X - X + c) -
            3 * P 1 +
          3 * (1 - c) * W 1 -
        34612 / 1000000 <
      4 * (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, S n) - (∑' n : ℕ, S n) := by
  intro X B W P S c E
  have hx : 0 < X := sq_pos_of_pos (by linarith only [hr])
  have hx1 : 1 ≤ X :=
    (by norm_num only : (1 : ℝ) ≤ 278 ^ 2).trans (pow_le_pow_left₀ (by norm_num only) hr 2)
  have hb : X ≤ B := le_mul_of_one_le_right hx.le (Real.one_le_exp (by norm_num only))
  have hi := (centered_integrand_continuous (b := X) hx (le_refl 1)).2
  have ho := (centered_integrand_continuous (b := B) hx hx1).2
  rw [← Set.uIcc_of_le hx1] at hi
  rw [← Set.uIcc_of_le hb] at ho
  have hs :=
    intervalIntegral.integral_add_adjacent_intervals
      (hi.intervalIntegrable (μ := MeasureTheory.volume)) ho.intervalIntegrable
  have h := quarter_integral_lower_570 hr hRH
  have he := quarter_outer_error_570 hr hRH
  dsimp only [X, B, W, P, S, c, E] at *
  linarith only [h, he, hs]

end PseudoPrime.PrimeTestBounds.MillerRabin
