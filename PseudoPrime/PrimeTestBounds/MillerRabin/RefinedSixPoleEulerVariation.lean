/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleEulerPrefixBound
public import PseudoPrime.Analysis.PowerLogKernel

/-! # Logarithmic variation of the refined Euler weight -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The normalized sixth-pole Euler weight on the real line, expressed as a
real power times a quadratic logarithmic polynomial. It agrees with the
natural-index weight and is the integrand of the double-Abel tail formula. -/
noncomputable def refinedEulerRealWeight (x : ℝ) : ℝ :=
  x ^ (-(79 / 50 : ℝ)) * (3 + (81 / 25 : ℝ) * Real.log x + (729 / 625 : ℝ) * (Real.log x) ^ 2) / 8

/-- The logarithmic slope of the refined Euler weight, equal to `x * w'(x)`
at positive `x`. Its explicit polynomial form retains the boundary term in
double partial summation. -/
noncomputable def refinedEulerSlope (x : ℝ) : ℝ :=
  x ^ (-(79 / 50 : ℝ)) *
      ((81 / 25 : ℝ) + (1458 / 625 : ℝ) * Real.log x -
        (79 / 50 : ℝ) * (3 + (81 / 25 : ℝ) * Real.log x + (729 / 625 : ℝ) * (Real.log x) ^ 2)) /
    8

/-- The derivative of the refined Euler logarithmic slope, expressed as a
negative real power times a quadratic logarithmic polynomial. It is the
density against the smoothed Chebyshev error in the Euler tail. -/
noncomputable def refinedEulerVariation (x : ℝ) : ℝ :=
  x ^ (-(79 / 50 : ℝ) - 1) *
      ((4549689 / 1562500 : ℝ) * (Real.log x) ^ 2 + (44793 / 62500 : ℝ) * Real.log x -
        (1041 / 2500 : ℝ)) /
    8

/-- At every positive point, the refined real Euler weight has derivative
its logarithmic slope divided by the input. Differentiate the real power and
logarithmic polynomial. This identifies the first Abel boundary term. -/
theorem refined_weight_derivative {x : ℝ} (hx : 0 < x) :
    HasDerivAt refinedEulerRealWeight (refinedEulerSlope x / x) x := by
  have hp := Real.hasDerivAt_rpow_const (p := -(79 / 50 : ℝ)) (Or.inl hx.ne')
  have hl := Real.hasDerivAt_log hx.ne'
  have hpoly :=
    ((hasDerivAt_const x (3 : ℝ)).add (hl.const_mul (81 / 25 : ℝ))).add
      ((hl.pow 2).const_mul (729 / 625 : ℝ))
  have h := (hp.mul hpoly).div_const 8
  convert h using 1
  · rfl
  · dsimp only [refinedEulerSlope]
    rw [Real.rpow_sub_one hx.ne' (-(79 / 50 : ℝ))]
    simp only [div_eq_mul_inv, Pi.add_apply, Pi.pow_apply, Nat.reduceSub, pow_one, Nat.cast_ofNat,
      zero_add]
    ring

/-- The logarithmic slope has the explicit variation density as derivative
at every positive point. Apply the product rule and collect the quadratic
logarithmic coefficients. This supplies the double-Abel kernel. -/
theorem refined_slope_derivative {x : ℝ} (hx : 0 < x) :
    HasDerivAt refinedEulerSlope (refinedEulerVariation x) x := by
  have hp := Real.hasDerivAt_rpow_const (p := -(79 / 50 : ℝ)) (Or.inl hx.ne')
  have hl := Real.hasDerivAt_log hx.ne'
  have hQ :=
    ((hasDerivAt_const x (3 : ℝ)).add (hl.const_mul (81 / 25 : ℝ))).add
      ((hl.pow 2).const_mul (729 / 625 : ℝ))
  have hS :=
    ((hasDerivAt_const x (81 / 25 : ℝ)).add (hl.const_mul (1458 / 625 : ℝ))).sub
      (hQ.const_mul (79 / 50 : ℝ))
  have h := (hp.mul hS).div_const 8
  convert h using 1
  · rfl
  · dsimp only [refinedEulerVariation]
    rw [Real.rpow_sub_one hx.ne' (-(79 / 50 : ℝ))]
    simp only [div_eq_mul_inv, Pi.add_apply, Pi.sub_apply, Pi.pow_apply, Nat.reduceSub, pow_one,
      Nat.cast_ofNat, zero_add]
    ring

/-- The real Euler weight agrees with the normalized natural-index weight.
The negative-power identity rewrites the denominator, including the total
zero convention. This connects the integral formulas to the Euler series. -/
theorem refined_weight_nat (n : ℕ) : refinedEulerRealWeight n = refinedSixEulerWeight n := by
  unfold refinedEulerRealWeight refinedSixEulerWeight
  rw [Real.rpow_neg (Nat.cast_nonneg n)]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The derivative of `t * w'(t)` is the refined variation density at every
positive point. Transfer the explicit slope identity on a neighborhood and
differentiate it. This is the second Abel derivative. -/
theorem refined_weight_log_variation {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t : ℝ ↦ t * deriv refinedEulerRealWeight t) (refinedEulerVariation x) x := by
  have he : (fun t : ℝ ↦ t * deriv refinedEulerRealWeight t) =ᶠ[nhds x] refinedEulerSlope := by
    filter_upwards [Ioi_mem_nhds hx] with t ht
    rw [(refined_weight_derivative ht).deriv, mul_div_cancel₀ _ ht.ne']
  exact (refined_slope_derivative hx).congr_of_eventuallyEq he

/-- The refined Euler variation density is nonnegative for inputs at least
three. The logarithm is at least one there, making the explicit quadratic
polynomial positive. This permits one-sided tail estimates beyond 1000. -/
theorem refined_variation_nonneg {x : ℝ} (hx : 3 ≤ x) : 0 ≤ refinedEulerVariation x := by
  have hx0 : 0 < x := by linarith only [hx]
  have hl : 1 ≤ Real.log x :=
    (Real.le_log_iff_exp_le hx0).mpr (by linarith only [Real.exp_one_lt_d9, hx])
  unfold refinedEulerVariation
  apply div_nonneg
  · apply mul_nonneg (Real.rpow_nonneg hx0.le _)
    nlinarith only [hl, sq_nonneg (Real.log x)]
  · norm_num only

/-- On a positive finite interval, the logarithmic refined variation integral
has the two exact weight and logarithmic-slope boundary terms. Apply the
smooth variation identity with the certified derivatives and continuity.
This is the scalar atom identity used in double partial summation. -/
theorem refined_log_variation_integral {v a b : ℝ} (hv : 0 < v) (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, Real.log (t / v) * refinedEulerVariation t) =
      Real.log (b / v) * refinedEulerSlope b - refinedEulerRealWeight b -
        (Real.log (a / v) * refinedEulerSlope a - refinedEulerRealWeight a) := by
  have hi :
    IntervalIntegrable (fun t : ℝ ↦ Real.log (t / v) * refinedEulerVariation t) MeasureTheory.volume
      a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    apply ContinuousOn.mul
    · intro t ht
      exact (Analysis.log_div_derivative hv (ha.trans_le ht.1)).continuousAt.continuousWithinAt
    · intro t ht
      have ht0 := ha.trans_le ht.1
      unfold refinedEulerVariation
      exact
        (((Real.continuousAt_rpow_const t (-(79 / 50 : ℝ) - 1) (Or.inl ht0.ne')).mul
                (((continuousAt_const.mul ((Real.continuousAt_log ht0.ne').pow 2)).add
                      (continuousAt_const.mul (Real.continuousAt_log ht0.ne'))).sub
                  continuousAt_const)).div_const
            8).continuousWithinAt
  have h :=
    Analysis.log_variation_integral hv ha hab (V := refinedEulerRealWeight) (P :=
      deriv refinedEulerRealWeight) (Q := refinedEulerVariation)
      (fun t ht ↦
        (refined_weight_derivative (ha.trans_le ht.1)).deriv ▸
          refined_weight_derivative (ha.trans_le ht.1))
      (fun t ht ↦ refined_weight_log_variation (ha.trans_le ht.1)) hi
  rw [(refined_weight_derivative ha).deriv,
    (refined_weight_derivative (ha.trans_le hab)).deriv] at h
  rw [mul_div_cancel₀ _ ha.ne', mul_div_cancel₀ _ (ha.trans_le hab).ne'] at h
  exact h

/-- A positive clipped-log atom through the upper endpoint has the exact
refined variation integral with lower endpoint `max a v`. Split at the atom
when necessary and use the smooth logarithmic formula. This supports the
finite Mangoldt sum before passage to the infinite tail. -/
theorem refined_clipped_log_integral {v a b : ℝ} (hv : 0 < v) (ha : 0 < a) (hab : a ≤ b)
    (hvb : v ≤ b) :
    (∫ t in a..b, Analysis.positiveLogRatio v t * refinedEulerVariation t) =
      (Real.log (b / v) * refinedEulerSlope b - refinedEulerRealWeight b) -
        (Real.log (max a v / v) * refinedEulerSlope (max a v) -
          refinedEulerRealWeight (max a v)) := by
  have hint {c d : ℝ} (hc : 0 < c) (hcd : c ≤ d) :
    IntervalIntegrable (fun t ↦ Analysis.positiveLogRatio v t * refinedEulerVariation t)
      MeasureTheory.volume c d := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hcd]
    apply ContinuousOn.mul (Analysis.positiveLogRatio_continuous hv).continuousOn
    intro t ht
    have ht0 := hc.trans_le ht.1
    unfold refinedEulerVariation
    exact
      (((Real.continuousAt_rpow_const t (-(79 / 50 : ℝ) - 1) (Or.inl ht0.ne')).mul
              (((continuousAt_const.mul ((Real.continuousAt_log ht0.ne').pow 2)).add
                    (continuousAt_const.mul (Real.continuousAt_log ht0.ne'))).sub
                continuousAt_const)).div_const
          8).continuousWithinAt
  by_cases hva : v ≤ a
  · rw [max_eq_left hva]
    have he :
      (∫ t in a..b, Analysis.positiveLogRatio v t * refinedEulerVariation t) =
        ∫ t in a..b, Real.log (t / v) * refinedEulerVariation t := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hab] at ht
      dsimp only
      rw [Analysis.positiveLogRatio_eq_log (hva.trans ht.1)]
    rw [he, refined_log_variation_integral hv ha hab]
  · have hav := (lt_of_not_ge hva).le
    rw [max_eq_right hav, ←
      intervalIntegral.integral_add_adjacent_intervals (hint ha hav) (hint hv hvb)]
    have hz : (∫ t in a..v, Analysis.positiveLogRatio v t * refinedEulerVariation t) = 0 := by
      calc
        _ = ∫ t in a..v, (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro t ht
          rw [Set.uIcc_of_le hav] at ht
          dsimp only
          rw [Analysis.positiveLogRatio_zero ht.2, zero_mul]
        _ = 0 := intervalIntegral.integral_zero
    have he :
      (∫ t in v..b, Analysis.positiveLogRatio v t * refinedEulerVariation t) =
        ∫ t in v..b, Real.log (t / v) * refinedEulerVariation t := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hvb] at ht
      dsimp only
      rw [Analysis.positiveLogRatio_eq_log ht.1]
    rw [hz, zero_add, he, refined_log_variation_integral hv hv hvb]

end PseudoPrime.PrimeTestBounds.MillerRabin
