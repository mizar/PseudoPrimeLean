/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.RiemannWeightedUpperBounds
public import PseudoPrime.LLS.RiemannWeightedBounds

/-! # Sharp global logarithmically weighted Mangoldt error under RH -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Under RH and x > 1, the logarithmically weighted sum is at least x minus
sqrt(x)/20, (1839/1000) log(x), and 21/20. Bound the zero mass and log(2 pi)
in the existing lower estimate. This retains the sharp square-root coefficient
needed for double partial summation with the exponential ramp. -/
theorem logWeightedMangoldtSum_ge_rational_refined {x : ℝ} (hRH : RiemannHypothesis) (hx : 1 < x) :
    x - Real.sqrt x / 20 - (1839 / 1000 : ℝ) * Real.log x - 21 / 20 ≤
      AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum x := by
  have hlo := llsRiemannWeightedLowerBound_of_riemannHypothesis hRH x hx
  have hm :=
    mul_le_mul_of_nonneg_right AnalyticNumberTheory.RiemannXi.riemannZeroMass_le_one_fortieth
      (add_nonneg (Real.sqrt_nonneg x) zero_le_one)
  have hl := mul_le_mul_of_nonneg_right Analysis.log_two_mul_pi_lt.le (Real.log_pos hx).le
  linarith only [hlo, hm, hl]

theorem logWeightedMangoldtSum_error_le_refined {x : ℝ} (hRH : RiemannHypothesis) (hx : 1 < x) :
    |AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum x - x| ≤
      Real.sqrt x / 20 + (1839 / 1000 : ℝ) * Real.log x + 21 / 20 := by
  have hlo := logWeightedMangoldtSum_ge_rational_refined hRH hx
  have hhi := logWeightedMangoldtSum_le_add_sqrt_twentieth hRH hx
  rw [abs_le]
  constructor <;> linarith only [hlo, hhi, Real.log_pos hx]

/-- At any real cutoff x <= 1, the logarithmically weighted sum vanishes.
Every positive index in the floor interval equals one, where von Mangoldt is zero.
This supplies the small-input case needed inside the error integral. -/
theorem logWeightedMangoldtSum_eq_zero_of_le_one {x : ℝ} (hx : x ≤ 1) :
    AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum x = 0 := by
  apply Finset.sum_eq_zero
  intro n hn
  have hupper : n ≤ 1 := (Finset.mem_Ioc.mp hn).2.trans ((Nat.floor_mono hx).trans_eq Nat.floor_one)
  have heq : n = 1 := Nat.le_antisymm hupper (Nat.succ_le_of_lt (Finset.mem_Ioc.mp hn).1)
  simp only [heq, AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm,
    ArithmeticFunction.vonMangoldt_apply_one, zero_mul]

/-- Under RH and at every positive x, the logarithmically weighted error is
at most sqrt(x)/20 + (1839/1000) log(max(1,x)) + 21/20. For x > 1 combine
the sharp one-sided bounds; otherwise the sum is zero. This global estimate
is the analytic error input for the smoothed coefficient-0.8 witness comparison. -/
theorem logWeightedMangoldtSum_error_le_refined_global (hRH : RiemannHypothesis) {x : ℝ}
    (hx : 0 < x) :
    |AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum x - x| ≤
      Real.sqrt x / 20 + (1839 / 1000 : ℝ) * Real.log (max 1 x) + 21 / 20 := by
  by_cases hlarge : 1 < x
  · rw [max_eq_right hlarge.le]
    exact logWeightedMangoldtSum_error_le_refined hRH hlarge
  · have hsmall := le_of_not_gt hlarge
    rw [logWeightedMangoldtSum_eq_zero_of_le_one hsmall, zero_sub, abs_neg, abs_of_pos hx,
      max_eq_left hsmall, Real.log_one, mul_zero, add_zero]
    linarith only [hsmall, Real.sqrt_nonneg x]

/-- Under RH, x>=1 and 0<=u<=99/40, bound the arithmetic error at xu by
sqrt(x)sqrt(u)/20 plus the logarithmic term at the common endpoint (99/40)x.
Apply the global sharp error, monotonicity of log, and sqrt(xu)=sqrt(x)sqrt(u).
At u=0 the sum vanishes. This is the input integrated against both ramp densities. -/
theorem logWeightedMangoldtSum_scaled_ramp_error (hRH : RiemannHypothesis) {x u : ℝ} (hx : 1 ≤ x)
    (hu : 0 ≤ u) (hub : u ≤ 99 / 40) :
    |AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) - x * u| ≤
      Real.sqrt x / 20 * Real.sqrt u + (1839 / 1000 : ℝ) * Real.log (x * (99 / 40)) + 21 / 20 := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hX : 1 ≤ x * (99 / 40) := by nlinarith only [hx]
  by_cases hu0 : 0 < u
  · have he := logWeightedMangoldtSum_error_le_refined_global hRH (mul_pos hx0 hu0)
    have hmax : max 1 (x * u) ≤ x * (99 / 40) := max_le hX (mul_le_mul_of_nonneg_left hub hx0.le)
    have hl := Real.log_le_log (zero_lt_one.trans_le (le_max_left (1 : ℝ) (x * u))) hmax
    rw [Real.sqrt_mul hx0.le] at he
    linarith only [he, hl]
  · have heq : u = 0 := le_antisymm (le_of_not_gt hu0) hu
    rw [heq, mul_zero, logWeightedMangoldtSum_eq_zero_of_le_one (by norm_num only), sub_self,
      abs_zero, Real.sqrt_zero, mul_zero]
    linarith only [Real.log_nonneg hX]

end PseudoPrime.LLS
