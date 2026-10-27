/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.LogWeightedDifferences
public import PseudoPrime.LLS.RiemannWeightedUpperBounds
public import PseudoPrime.LLS.RiemannWeightedBounds

/-! # RH bounds for Chebyshev sums used in truncated kernel estimates

The logarithmic zeta explicit formula has square-root error. Elementary finite
differences give short-interval Chebyshev bounds. Choosing a three-quarter-power
step yields a quantitative error for the unsmoothed sum without an external PNT.
-/

@[expose] public section

namespace PseudoPrime.LLS

/-- Under RH and x > 1, bound the difference of the logarithmically weighted
Mangoldt sum and x by explicit logarithmic and square-root terms. Combine the
proved upper and lower logarithmic zeta bounds; all omitted terms are nonnegative.
This is the two-sided input for recovering unsmoothed Mangoldt partial sums. -/
theorem logWeightedMangoldtSum_error_le_log_sqrt (hRH : RiemannHypothesis) {x : ℝ} (hx : 1 < x) :
    |AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum x - x| ≤
      Real.log (2 * Real.pi) * Real.log x + 1 +
        2 * AnalyticNumberTheory.RiemannXi.riemannZeroMass * (Real.sqrt x + 1) +
        Real.sqrt x / 20 := by
  have hlo := llsRiemannWeightedLowerBound_of_riemannHypothesis hRH x hx
  have hhi := logWeightedMangoldtSum_le_add_sqrt_twentieth hRH hx
  have hl :=
    mul_nonneg (Real.log_nonneg (by nlinarith only [Real.pi_gt_three] : 1 ≤ 2 * Real.pi))
      (Real.log_pos hx).le
  have hm : 0 ≤ AnalyticNumberTheory.RiemannXi.riemannZeroMass := abs_nonneg _
  have hs := mul_nonneg hm (add_nonneg (Real.sqrt_nonneg x) zero_le_one)
  rw [abs_le]
  constructor <;> nlinarith only [hlo, hhi, hl, hs, Real.sqrt_nonneg x]

/-- Under RH, there is a positive constant C such that the logarithmically
weighted Mangoldt sum differs from x by at most C sqrt(x) for x > 1. Apply the
logarithmic error bound and log(x) <= 2 sqrt(x), absorbing the fixed terms using
sqrt(x) >= 1. This gives the rate used in finite-difference Chebyshev bounds. -/
theorem exists_logWeightedMangoldtSum_error_le_sqrt (hRH : RiemannHypothesis) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ {x : ℝ},
          1 < x →
            |AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum x - x| ≤ C * Real.sqrt x := by
  let L := Real.log (2 * Real.pi)
  let b := AnalyticNumberTheory.RiemannXi.riemannZeroMass
  have hL : 0 ≤ L := Real.log_nonneg (by nlinarith only [Real.pi_gt_three])
  have hb : 0 ≤ b := abs_nonneg _
  refine ⟨2 * L + 4 * b + 2, by linarith only [hL, hb], ?_⟩
  intro x hx
  have hs : 1 ≤ Real.sqrt x := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hx.le
  have hl := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr (zero_lt_one.trans hx))
  rw [Real.log_sqrt (zero_lt_one.trans hx).le] at hl
  have hlog : Real.log x ≤ 2 * Real.sqrt x := by linarith only [hl]
  have hmul := mul_le_mul_of_nonneg_left hlog hL
  have hbmul := mul_le_mul_of_nonneg_left hs hb
  have he := logWeightedMangoldtSum_error_le_log_sqrt hRH hx
  change
    |AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum x - x| ≤
      L * Real.log x + 1 + 2 * b * (Real.sqrt x + 1) + Real.sqrt x / 20 at he
  nlinarith only [he, hmul, hbmul, hs]

/-- Under RH, a positive constant C bounds psi at the endpoints of every
interval 1 < x < y by the displayed square-root errors divided by y-x. Apply the
arithmetic finite-difference comparison to the uniform smoothed error. The
interval length remains free for the subsequent power-sized choice. -/
theorem exists_psi_short_interval_bounds (hRH : RiemannHypothesis) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ {x y : ℝ},
          1 < x →
            x < y →
            Chebyshev.psi x ≤ y + C * (Real.sqrt x + Real.sqrt y) * y / (y - x) ∧
              x - C * (Real.sqrt x + Real.sqrt y) * x / (y - x) ≤ Chebyshev.psi y := by
  obtain ⟨C, hC, hb⟩ := exists_logWeightedMangoldtSum_error_le_sqrt hRH
  refine ⟨C, hC, ?_⟩
  intro x y hx hxy
  have h :=
    AnalyticNumberTheory.Arithmetic.psi_bounds_of_logWeighted_error_without_log
      (zero_lt_one.trans hx) hxy (hb hx) (hb (hx.trans hxy))
  simpa only [← mul_add] using h

/-- Under RH, a positive constant bounds abs(psi(x)-x) by
C sqrt(x) sqrt(sqrt(x)) for every x >= 16. Represent x as the fourth power of
its iterated square root and apply the short-interval bound with a cubic step.
This supplies a quantitative Mangoldt partial-sum estimate for truncating the
general Mellin kernel in the proof of Proposition 6.1; no PNT hypothesis remains. -/
theorem exists_psi_error_le_three_quarter (hRH : RiemannHypothesis) :
    ∃ D : ℝ,
      0 < D ∧
        ∀ {x : ℝ}, 16 ≤ x → |Chebyshev.psi x - x| ≤ D * Real.sqrt x * Real.sqrt (Real.sqrt x) := by
  obtain ⟨C, hC, hb⟩ := exists_logWeightedMangoldtSum_error_le_sqrt hRH
  refine ⟨1 + 6 * C, by linarith only [hC], ?_⟩
  intro x hx
  exact
    AnalyticNumberTheory.Arithmetic.psi_error_le_three_quarter_of_logWeighted_error hC.le
      (fun hu ↦ hb hu) hx

/-- Under RH and x >= 16, the normalized Chebyshev error is at most a fixed
positive constant divided by sqrt(sqrt(x)). Divide the three-quarter-power estimate
by x and cancel the square-root factors. This yields an explicit majorant tending
to zero for the Chebyshev asymptotic. -/
theorem exists_psi_ratio_error_le_quarter (hRH : RiemannHypothesis) :
    ∃ D : ℝ,
      0 < D ∧ ∀ {x : ℝ}, 16 ≤ x → |Chebyshev.psi x / x - 1| ≤ D / Real.sqrt (Real.sqrt x) := by
  obtain ⟨D, hD, hb⟩ := exists_psi_error_le_three_quarter hRH
  refine ⟨D, hD, ?_⟩
  intro x hx
  have hx0 : 0 < x := (by norm_num only : (0 : ℝ) < 16).trans_le hx
  have hr : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hs : 0 < Real.sqrt (Real.sqrt x) := Real.sqrt_pos.mpr hr
  rw [div_sub_one hx0.ne', abs_div, abs_of_pos hx0]
  have h := div_le_div_of_nonneg_right (hb hx) hx0.le
  have he : D * Real.sqrt x * Real.sqrt (Real.sqrt x) / x = D / Real.sqrt (Real.sqrt x) := by
    apply (div_eq_div_iff hx0.ne' hs.ne').mpr
    have hsq := Real.sq_sqrt hr.le
    have hx2 := Real.sq_sqrt hx0.le
    calc
      _ = D * Real.sqrt x * (Real.sqrt (Real.sqrt x) ^ 2) := by ring
      _ = D * x := by rw [hsq, mul_assoc, ← pow_two, hx2]
  exact h.trans_eq he

/-- Under RH, psi(x)/x tends to one as x tends to infinity. Squeeze the absolute
normalized error between zero and the proved inverse-fourth-root majorant.
This is the prime-power asymptotic used to approximate continuous cutoff weights. -/
theorem tendsto_psi_div_self_of_riemannHypothesis (hRH : RiemannHypothesis) :
    Filter.Tendsto (fun x : ℝ ↦ Chebyshev.psi x / x) Filter.atTop (nhds 1) := by
  obtain ⟨D, _, hb⟩ := exists_psi_ratio_error_le_quarter hRH
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hu : ∀ᶠ x : ℝ in Filter.atTop, ‖Chebyshev.psi x / x - 1‖ ≤ D / Real.sqrt (Real.sqrt x) :=
    (Filter.eventually_ge_atTop (16 : ℝ)).mono
      (fun x hx ↦ by simpa only [Real.norm_eq_abs] using hb hx)
  exact
    squeeze_zero' (Filter.Eventually.of_forall (fun x ↦ norm_nonneg _)) hu
      ((Real.tendsto_sqrt_atTop.comp Real.tendsto_sqrt_atTop).const_div_atTop D)

/-- Under RH, for a fixed positive scale c, psi(c*x)/x tends to c. Compose the
Chebyshev limit with dilation, multiply by c, and cancel c at positive x.
This gives the endpoint limits for scaled finite intervals. -/
theorem tendsto_psi_scaled_div_self (hRH : RiemannHypothesis) {c : ℝ} (hc : 0 < c) :
    Filter.Tendsto (fun x : ℝ ↦ Chebyshev.psi (c * x) / x) Filter.atTop (nhds c) := by
  have ht :=
    ((tendsto_psi_div_self_of_riemannHypothesis hRH).comp
          (Filter.Tendsto.const_mul_atTop hc Filter.tendsto_id)).mul_const
      c
  simp only [Function.comp_apply, one_mul] at ht
  apply Filter.Tendsto.congr' _ ht
  apply (Filter.eventually_gt_atTop (0 : ℝ)).mono
  intro x hx
  calc
    Chebyshev.psi (c * x) / (c * x) * c = (Chebyshev.psi (c * x) * c) / (c * x) := by ring
    _ = Chebyshev.psi (c * x) / x := by
      apply (div_eq_div_iff (mul_ne_zero hc.ne' hx.ne') hx.ne').mpr
      ring

/-- Under RH and 0 < a <= b, the Mangoldt sum over a*x < n <= b*x, divided
by x, tends to b-a. Express the finite sum by the difference of endpoint psi
values and apply their scaled limits. This proves convergence for interval
step weights, the first approximation step for a general truncated Mellin kernel. -/
theorem tendsto_mangoldt_scaled_interval_sum (hRH : RiemannHypothesis) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) :
    Filter.Tendsto
      (fun x : ℝ ↦ (∑ n ∈ Finset.Ioc ⌊a * x⌋₊ ⌊b * x⌋₊, ArithmeticFunction.vonMangoldt n) / x)
      Filter.atTop (nhds (b - a)) := by
  have ht :=
    (tendsto_psi_scaled_div_self hRH (ha.trans_le hab)).sub (tendsto_psi_scaled_div_self hRH ha)
  apply Filter.Tendsto.congr' _ ht
  apply (Filter.eventually_ge_atTop (0 : ℝ)).mono
  intro x hx
  dsimp only
  rw [← sub_div,
    AnalyticNumberTheory.Arithmetic.mangoldt_interval_sum_eq_psi_sub
      (mul_le_mul_of_nonneg_right hab hx)]

end PseudoPrime.LLS
