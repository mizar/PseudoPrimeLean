/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100PhaseBounds
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100PhasePreciseArithmetic

/-! # Narrow phase logarithm intervals -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- If the narrow rational check succeeds, the phase logarithm differs from the true logarithm
of its rounded argument by at most `4/1000000000`. The Taylor interval is checked exactly. -/
theorem endpoint_precise_log_sound (t : ℚ) (h : endpointPhasePreciseCheck t = true) :
    |Real.log (endpointPhaseArgument t : ℝ) - (endpointPhaseLog t : ℝ)| ≤ 4 / 1000000000 := by
  have hl := Analysis.rationalLogIntervalCheck_sound h
  simp only [Rat.cast_sub, Rat.cast_add, Rat.cast_div, Rat.cast_ofNat] at hl
  refine abs_le.mpr ?_
  constructor <;> linarith only [hl.1, hl.2]

/-- If both phase checks succeed at `0 ≤ t ≤ 100`, the narrow approximation differs from
`log(t/(2*pi))` by at most `6/1000000000`. The argument and Taylor errors are combined. -/
theorem endpoint_precise_true_log (t : ℚ) (ht0 : 0 ≤ t) (ht : t ≤ 100)
    (hcheck : endpointPhaseLogCheck t = true) (hprecise : endpointPhasePreciseCheck t = true) :
    |Real.log ((t : ℝ) / (2 * Real.pi)) - (endpointPhaseLog t : ℝ)| ≤ 6 / 1000000000 := by
  have ha := endpoint_phase_argument_error t ht0 ht
  have hc := endpoint_phase_log_sound t hcheck
  have hp := endpoint_precise_log_sound t hprecise
  have hq : (2 : ℝ) ≤ endpointPhaseArgument t := by exact_mod_cast hc.1
  have hx : (1 : ℝ) ≤ (t : ℝ) / (2 * Real.pi) := by
    have hh := abs_le.mp ha
    linarith only [hq, hh.1]
  have hy : (1 : ℝ) ≤ endpointPhaseArgument t := by linarith only [hq]
  have hl := abs_log_sub_le ((t : ℝ) / (2 * Real.pi)) (endpointPhaseArgument t) hx hy
  have hh :=
    abs_sub_le (Real.log ((t : ℝ) / (2 * Real.pi))) (Real.log (endpointPhaseArgument t))
      (endpointPhaseLog t)
  linarith only [ha, hp, hl, hh]

/-- For `0 ≤ t ≤ 31` and successful phase checks, the rational elementary phase is within
`94/1000000000` of the true phase. This narrower estimate resolves the smallest endpoint margin. -/
theorem endpoint_precise_theta (t : ℚ) (ht0 : 0 ≤ t) (ht : t ≤ 31)
    (hcheck : endpointPhaseLogCheck t = true) (hprecise : endpointPhasePreciseCheck t = true) :
    |backlundThetaMain t - (endpointTheta t : ℝ)| ≤ 94 / 1000000000 := by
  have ht100 : t ≤ 100 := by linarith only [ht]
  have hl := endpoint_precise_true_log t ht0 ht100 hcheck hprecise
  have hp : |Real.pi - (endpointPi : ℝ)| ≤ 1 / 1000000000000000 := by
    rw [abs_le]
    norm_num only [endpointPi, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat]
    constructor <;> linarith only [Real.pi_gt_d20, Real.pi_lt_d20]
  have ht0R : (0 : ℝ) ≤ t := by exact_mod_cast ht0
  have htR : (t : ℝ) ≤ 31 := by exact_mod_cast ht
  have hm :=
    mul_le_mul (show (t : ℝ) / 2 ≤ 31 / 2 by linarith only [htR]) hl (abs_nonneg _)
      (by norm_num only : (0 : ℝ) ≤ 31 / 2)
  have heq :
    backlundThetaMain t - (endpointTheta t : ℝ) =
      ((t : ℝ) / 2) * (Real.log ((t : ℝ) / (2 * Real.pi)) - (endpointPhaseLog t : ℝ)) -
        (Real.pi - (endpointPi : ℝ)) / 8 := by
    simp only [backlundThetaMain, endpointTheta, Rat.cast_sub, Rat.cast_mul, Rat.cast_div,
      Rat.cast_ofNat]
    ring
  rw [heq]
  have hh :=
    abs_sub (((t : ℝ) / 2) * (Real.log ((t : ℝ) / (2 * Real.pi)) - (endpointPhaseLog t : ℝ)))
      ((Real.pi - (endpointPi : ℝ)) / 8)
  rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ t / 2 by linarith only [ht0R]), abs_div,
    abs_of_pos (show (0 : ℝ) < 8 by norm_num only)] at hh
  linarith only [hm, hp, hh]

/-- Under the two checked logarithm enclosures and `0 ≤ t ≤ 31`, the rounded phase factor
differs from the analytic phase factor by at most `95/1000000000`. -/
theorem norm_endpoint_precise_phase (t : ℚ) (ht0 : 0 ≤ t) (ht : t ≤ 31)
    (hcheck : endpointPhaseLogCheck t = true) (hprecise : endpointPhasePreciseCheck t = true) :
    ‖Complex.exp ((backlundThetaMain t : ℂ) * Complex.I) -
          Analysis.rationalComplexCast
            (Analysis.rationalScaledPhase (10 ^ 15) (endpointTheta t) 16 11)‖ ≤
      95 / 1000000000 := by
  have ht100 : t ≤ 100 := by linarith only [ht]
  have hθ := endpoint_precise_theta t ht0 ht hcheck hprecise
  have h1 := Analysis.norm_phase_exp_sub_le (backlundThetaMain t) (endpointTheta t)
  have h2 := norm_endpoint_phase (endpointTheta t) (endpoint_theta_range t ht0 ht100 hcheck)
  rw [← Complex.ofReal_ratCast] at h2
  have hh :=
    norm_sub_le_norm_sub_add_norm_sub (Complex.exp (Complex.I * (backlundThetaMain t : ℂ)))
      (Complex.exp (Complex.I * (((endpointTheta t : ℝ) : ℂ))))
      (Analysis.rationalComplexCast
        (Analysis.rationalScaledPhase (10 ^ 15) (endpointTheta t) 16 11))
  rw [mul_comm]
  exact hh.trans ((add_le_add (h1.trans hθ) h2).trans (by norm_num only))

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
