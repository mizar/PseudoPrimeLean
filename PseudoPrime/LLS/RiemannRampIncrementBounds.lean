/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.RiemannWeightedErrorBounds
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.LogWeightedIncrementBounds

/-! # RH increment bounds for pairing the two ramp jumps -/

@[expose] public section

namespace PseudoPrime.LLS

/-- A common RH smoothed-error envelope up to (101/40)x at scale x at least one.
The slightly enlarged endpoint covers the centered finite-difference stencil.
It retains the sharp square-root term rather than a global sqrt-only constant. -/
noncomputable def rampExtendedSmoothedError (x : ℝ) : ℝ :=
  (2 / 25 : ℝ) * Real.sqrt x + (1839 / 1000 : ℝ) * Real.log ((101 / 40 : ℝ) * x) + 21 / 20

/-- Under RH, x at least one and positive t at most (101/40)x, the smoothed
Mangoldt error is bounded by the common extended-ramp envelope.
Bound sqrt(t) by (8/5)sqrt(x) and the logarithm by the enlarged endpoint.
This supplies all three stencil values for a Chebyshev estimate. -/
theorem logWeighted_error_le_extended_ramp (hRH : RiemannHypothesis) {x t : ℝ} (hx : 1 ≤ x)
    (ht : 0 < t) (htb : t ≤ (101 / 40 : ℝ) * x) :
    |AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t - t| ≤
      rampExtendedSmoothedError x := by
  have hx0 := zero_lt_one.trans_le hx
  have he := logWeightedMangoldtSum_error_le_refined_global hRH ht
  have hs : Real.sqrt t ≤ (8 / 5 : ℝ) * Real.sqrt x := by
    apply Real.sqrt_le_iff.mpr
    exact
      ⟨mul_nonneg (by norm_num only) (Real.sqrt_nonneg x), by
        nlinarith only [htb, Real.sq_sqrt hx0.le]⟩
  have hmax : max 1 t ≤ (101 / 40 : ℝ) * x := by exact max_le (by linarith only [hx]) htb
  have hl := Real.log_le_log (zero_lt_one.trans_le (le_max_left (1 : ℝ) t)) hmax
  unfold rampExtendedSmoothedError
  linarith only [he, hs, hl]

/-- Under RH and x at least one, psi(t)-t has absolute value at most
x/20+101E(x) throughout the short ramp. Use the smoothed sums at t-x/20,
t and t+x/20 and positivity of Mangoldt weights. This quantitative stencil
bound avoids the coarse global three-quarter-power constant. -/
theorem psi_error_le_extended_ramp (hRH : RiemannHypothesis) {x t : ℝ} (hx : 1 ≤ x)
    (hta : (247 / 100 : ℝ) * x ≤ t) (htb : t ≤ (99 / 40 : ℝ) * x) :
    |Chebyshev.psi t - t| ≤ x / 20 + 101 * rampExtendedSmoothedError x := by
  have hx0 := zero_lt_one.trans_le hx
  have hs : 0 < x / 20 := div_pos hx0 (by norm_num only)
  have ht0 : 0 < t := by nlinarith only [hta, hx]
  have hl0 : 0 < t - x / 20 := by nlinarith only [hta, hx]
  have hh0 : 0 < t + x / 20 := by linarith only [ht0, hs]
  have hb1 :=
    logWeighted_error_le_extended_ramp hRH hx hl0
      (by linarith only [htb, hx] : t - x / 20 ≤ (101 / 40 : ℝ) * x)
  have hb2 :=
    logWeighted_error_le_extended_ramp hRH hx ht0
      (by linarith only [htb, hx] : t ≤ (101 / 40 : ℝ) * x)
  have hb3 :=
    logWeighted_error_le_extended_ramp hRH hx hh0
      (by linarith only [htb] : t + x / 20 ≤ (101 / 40 : ℝ) * x)
  have hE := (abs_nonneg (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t - t)).trans hb2
  have hlo :=
    (AnalyticNumberTheory.Arithmetic.psi_bounds_of_logWeighted_error_without_log hl0
        (by linarith only [hs] : t - x / 20 < t) hb1 hb2).2
  have hhi :=
    (AnalyticNumberTheory.Arithmetic.psi_bounds_of_logWeighted_error_without_log ht0
        (by linarith only [hs] : t < t + x / 20) hb2 hb3).1
  rw [show t - (t - x / 20) = x / 20 by ring] at hlo
  rw [show t + x / 20 - t = x / 20 by ring] at hhi
  have hcap :
    (rampExtendedSmoothedError x + rampExtendedSmoothedError x) * (t + x / 20) / (x / 20) ≤
      101 * rampExtendedSmoothedError x := by
    rw [div_le_iff₀ hs]
    have hm := mul_le_mul_of_nonneg_left htb hE
    nlinarith only [hm]
  have hcapl :
    (rampExtendedSmoothedError x + rampExtendedSmoothedError x) * (t - x / 20) / (x / 20) ≤
      101 * rampExtendedSmoothedError x := by
    have hm :=
      mul_le_mul_of_nonneg_left (show t - x / 20 ≤ t + x / 20 by linarith only [hs])
        (show 0 ≤ rampExtendedSmoothedError x + rampExtendedSmoothedError x by linarith only [hE])
    exact (div_le_div_of_nonneg_right hm hs.le).trans hcap
  rw [abs_le]
  constructor <;> linarith only [hlo, hhi, hcap, hcapl]

/-- The short-ramp increment allowance ((11/200)x+101E(x))/494.
It combines the two endpoint Chebyshev bounds with the ramp width and ratio.
The signed jump estimate uses this increment instead of two full error bounds. -/
noncomputable def rampSmoothedIncrementError (x : ℝ) : ℝ :=
  ((11 / 200 : ℝ) * x + 101 * rampExtendedSmoothedError x) / 494

/-- Under RH and x at least one, the smoothed-error increment between
(247/100)x and (99/40)x is bounded by the explicit increment allowance.
Insert the two Chebyshev stencil bounds into the generic finite-difference
increment lemma. This closes the paired-jump arithmetic input at every scale. -/
theorem logWeighted_ramp_error_increment (hRH : RiemannHypothesis) {x : ℝ} (hx : 1 ≤ x) :
    |(AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * (99 / 40)) - x * (99 / 40)) -
          (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * (247 / 100)) -
            x * (247 / 100))| ≤
      rampSmoothedIncrementError x := by
  have hx0 := zero_lt_one.trans_le hx
  have hp1 :=
    psi_error_le_extended_ramp hRH hx (by linarith only : (247 / 100 : ℝ) * x ≤ x * (247 / 100))
      (by linarith only [hx] : x * (247 / 100) ≤ (99 / 40 : ℝ) * x)
  have hp2 :=
    psi_error_le_extended_ramp hRH hx (by linarith only [hx] : (247 / 100 : ℝ) * x ≤ x * (99 / 40))
      (by linarith only : x * (99 / 40) ≤ (99 / 40 : ℝ) * x)
  have h :=
    AnalyticNumberTheory.Arithmetic.logWeighted_error_increment_le_of_psi_bounds
      (by nlinarith only [hx] : (0 : ℝ) < x * (247 / 100))
      (by nlinarith only [hx] : x * (247 / 100) ≤ x * (99 / 40)) hp1 hp2
  have he :
    ((x * (99 / 40) - x * (247 / 100)) + (x / 20 + 101 * rampExtendedSmoothedError x)) *
          (x * (99 / 40) - x * (247 / 100)) /
        (x * (247 / 100)) =
      rampSmoothedIncrementError x := by
    unfold rampSmoothedIncrementError
    field_simp [hx0.ne']
    ring
  rw [he] at h
  exact h

end PseudoPrime.LLS
