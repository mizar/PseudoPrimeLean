/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100PrecisePhaseArithmetic
import PseudoPrime.Analysis.PreciseLogBounds
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100PowerBounds
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.BacklundTheta
import Mathlib.Analysis.Real.Pi.Bounds
import PseudoPrime.Analysis.RealLog

/-! # Soundness of the precise endpoint phase logarithm check -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- For real inputs at least one, the logarithm is one-Lipschitz. Tangent-line bounds on
both inputs give the estimate used to transfer rounded phase arguments. -/
theorem abs_precise_log_sub_le (x y : ℝ) (hx : 1 ≤ x) (hy : 1 ≤ y) :
    |Real.log x - Real.log y| ≤ |x - y| := by
  have hx0 : 0 < x := by linarith only [hx]
  have hy0 : 0 < y := by linarith only [hy]
  have hxy := Analysis.log_le_log_add_sub_div hy0 hx0
  have hyx := Analysis.log_le_log_add_sub_div hx0 hy0
  by_cases h : x ≤ y
  · have hyx0 : 0 ≤ y - x := sub_nonneg.mpr h
    have hh : (y - x) / x ≤ y - x := by
      rw [div_le_iff₀ hx0]
      nlinarith only [hx, hyx0]
    have hl := Real.log_le_log hx0 h
    rw [abs_le, abs_of_nonpos (sub_nonpos.mpr h)]
    constructor <;> linarith only [hyx, hh, hl]
  · have hxy0 : 0 ≤ x - y := sub_nonneg.mpr (le_of_not_ge h)
    have hh : (x - y) / y ≤ x - y := by
      rw [div_le_iff₀ hy0]
      nlinarith only [hy, hxy0]
    have hl := Real.log_le_log hy0 (le_of_not_ge h)
    rw [abs_le, abs_of_nonneg hxy0]
    constructor <;> linarith only [hxy, hh, hl]

/-- For `0 ≤ t ≤ 100`, replacing pi by the rational phase input changes `t/(2*pi)` by at most
`1/10^12`. The proof uses rational pi bounds and keeps the positive denominators explicit. -/
theorem endpoint_precise_pi_error (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ 100) :
    |t / (2 * Real.pi) - t / (2 * (endpointPi : ℝ))| ≤ 1 / 1000000000000 := by
  have hp : (3 : ℝ) ≤ Real.pi := by linarith only [Real.pi_gt_d20]
  have hq : (3 : ℝ) ≤ (endpointPi : ℝ) := by
    norm_num only [endpointPi, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat]
  have hdiff : |(endpointPi : ℝ) - Real.pi| ≤ 1 / 1000000000000000 := by
    rw [abs_le]
    norm_num only [endpointPi, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat]
    constructor <;> linarith only [Real.pi_gt_d20, Real.pi_lt_d20]
  have hden : (18 : ℝ) ≤ 2 * Real.pi * (endpointPi : ℝ) := by nlinarith only [hp, hq]
  have hprod := mul_le_mul ht hdiff (abs_nonneg _) (by norm_num only : (0 : ℝ) ≤ 100)
  have heq :
    t / (2 * Real.pi) - t / (2 * (endpointPi : ℝ)) =
      t * ((endpointPi : ℝ) - Real.pi) / (2 * Real.pi * (endpointPi : ℝ)) := by
    field_simp
  rw [heq, abs_div, abs_mul, abs_of_nonneg ht0,
    abs_of_pos (show 0 < 2 * Real.pi * (endpointPi : ℝ) by linarith only [hden])]
  apply (div_le_iff₀ (by linarith only [hden])).2
  nlinarith only [hden, hprod]

/-- For `0 ≤ t ≤ 100`, the rounded rational argument differs from `t/(2*pi)` by at most
`1/500000000000`. Combine the pi approximation and one downward grid-rounding error. -/
theorem endpoint_precise_arg_error (t : ℚ) (ht0 : 0 ≤ t) (ht : t ≤ 100) :
    |(t : ℝ) / (2 * Real.pi) - (endpointPreciseArgument t : ℝ)| ≤ 1 / 500000000000 := by
  have ht0R : (0 : ℝ) ≤ t := by exact_mod_cast ht0
  have htR : (t : ℝ) ≤ 100 := by exact_mod_cast ht
  have hp := endpoint_precise_pi_error t ht0R htR
  have hg :=
    Analysis.rationalGridFloor_error (by norm_num only : 0 < 10 ^ 12) (t / (2 * endpointPi))
  have hgR := (Rat.cast_le (K := ℝ)).mpr hg
  norm_num only [Rat.cast_abs, Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_natCast,
    Rat.cast_mul, Rat.cast_ofNat, Nat.cast_pow, Nat.cast_ofNat] at hgR
  change
    |(t : ℝ) / (2 * (endpointPi : ℝ)) - (endpointPreciseArgument t : ℝ)| ≤
      (1 / 1000000000000 : ℝ) at hgR
  have h :=
    abs_sub_le ((t : ℝ) / (2 * Real.pi)) ((t : ℝ) / (2 * (endpointPi : ℝ)))
      (endpointPreciseArgument t : ℝ)
  linarith only [hp, hgR, h]

/-- A successful rational phase check places its argument between 2 and 16 and bounds the
logarithm approximation by `1/100000000000`. The rational Taylor enclosure supplies the real
logarithm inequality without relying on a table of logarithms. -/
theorem endpoint_precise_phase_log_sound (t : ℚ) (h : endpointPrecisePhaseCheck t = true) :
    2 ≤ endpointPreciseArgument t ∧
      endpointPreciseArgument t ≤ 16 ∧
      |Real.log (endpointPreciseArgument t : ℝ) - (endpointPrecisePhaseLog t : ℝ)| ≤
        1 / 100000000000 := by
  have hc := Bool.and_eq_true_iff.mp h
  have hr : 2 ≤ endpointPreciseArgument t ∧ endpointPreciseArgument t ≤ 16 := of_decide_eq_true hc.1
  have hl := Analysis.rational_precise_log_check_sound hc.2
  simp only [Rat.cast_sub, Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at hl
  refine ⟨hr.1, hr.2, abs_le.mpr ?_⟩
  constructor <;> linarith only [hl.1, hl.2]

/-- A successful phase logarithm check at `0 ≤ t ≤ 100` approximates the true logarithm
`log(t/(2*pi))` within `3/250000000000`. The two errors come from the argument rounding and
the rational logarithm certificate. -/
theorem endpoint_precise_phase_true_log (t : ℚ) (ht0 : 0 ≤ t) (ht : t ≤ 100)
    (hcheck : endpointPrecisePhaseCheck t = true) :
    |Real.log ((t : ℝ) / (2 * Real.pi)) - (endpointPrecisePhaseLog t : ℝ)| ≤ 3 / 250000000000 := by
  have ha := endpoint_precise_arg_error t ht0 ht
  have hc := endpoint_precise_phase_log_sound t hcheck
  have hq : (2 : ℝ) ≤ endpointPreciseArgument t := by exact_mod_cast hc.1
  have hx : (1 : ℝ) ≤ (t : ℝ) / (2 * Real.pi) := by
    have hh := abs_le.mp ha
    linarith only [hq, hh.1]
  have hy : (1 : ℝ) ≤ endpointPreciseArgument t := by linarith only [hq]
  have hl := abs_precise_log_sub_le ((t : ℝ) / (2 * Real.pi)) (endpointPreciseArgument t) hx hy
  have hh :=
    abs_sub_le (Real.log ((t : ℝ) / (2 * Real.pi))) (Real.log (endpointPreciseArgument t))
      (endpointPrecisePhaseLog t)
  linarith only [ha, hc.2.2, hl, hh]

/-- When the rational logarithm check succeeds for `0 ≤ t ≤ 100`, the elementary Gamma
phase differs from its rational approximation by at most `1/1000000000`. The bound combines
the logarithm and pi errors and is used before the rounded phase exponentiation. -/
theorem endpoint_precise_theta_error (t : ℚ) (ht0 : 0 ≤ t) (ht : t ≤ 100)
    (hcheck : endpointPrecisePhaseCheck t = true) :
    |backlundThetaMain t - (endpointPreciseTheta t : ℝ)| ≤ 1 / 1000000000 := by
  have hl := endpoint_precise_phase_true_log t ht0 ht hcheck
  have hp : |Real.pi - (endpointPi : ℝ)| ≤ 1 / 1000000000000000 := by
    rw [abs_le]
    norm_num only [endpointPi, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat]
    constructor <;> linarith only [Real.pi_gt_d20, Real.pi_lt_d20]
  have ht0R : (0 : ℝ) ≤ t := by exact_mod_cast ht0
  have htR : (t : ℝ) ≤ 100 := by exact_mod_cast ht
  have hm :=
    mul_le_mul (show (t : ℝ) / 2 ≤ 50 by linarith only [htR]) hl (abs_nonneg _)
      (by norm_num only : (0 : ℝ) ≤ 50)
  have heq :
    backlundThetaMain t - (endpointPreciseTheta t : ℝ) =
      ((t : ℝ) / 2) * (Real.log ((t : ℝ) / (2 * Real.pi)) - (endpointPrecisePhaseLog t : ℝ)) -
        (Real.pi - (endpointPi : ℝ)) / 8 := by
    simp only [backlundThetaMain, endpointPreciseTheta, Rat.cast_sub, Rat.cast_mul, Rat.cast_div,
      Rat.cast_ofNat]
    ring
  rw [heq]
  have hh :=
    abs_sub (((t : ℝ) / 2) * (Real.log ((t : ℝ) / (2 * Real.pi)) - (endpointPrecisePhaseLog t : ℝ)))
      ((Real.pi - (endpointPi : ℝ)) / 8)
  rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ t / 2 by linarith only [ht0R]), abs_div,
    abs_of_pos (show (0 : ℝ) < 8 by norm_num only)] at hh
  linarith only [hm, hp, hh]

/-- If the phase check succeeds for `0 ≤ t ≤ 100`, the rational phase has absolute value at
most 700. This supplies the range hypothesis for the rounded phase exponential. -/
theorem endpoint_precise_theta_range (t : ℚ) (ht0 : 0 ≤ t) (ht : t ≤ 100)
    (h : endpointPrecisePhaseCheck t = true) : |(endpointPreciseTheta t : ℝ)| ≤ 700 := by
  have ht0R : (0 : ℝ) ≤ t := by exact_mod_cast ht0
  have htR : (t : ℝ) ≤ 100 := by exact_mod_cast ht
  have hc := endpoint_precise_phase_log_sound t h
  have hq0 : (2 : ℝ) ≤ endpointPreciseArgument t := by exact_mod_cast hc.1
  have hq1 : (endpointPreciseArgument t : ℝ) ≤ 16 := by exact_mod_cast hc.2.1
  have hlog0 : 0 ≤ Real.log (endpointPreciseArgument t : ℝ) :=
    Real.log_nonneg (by linarith only [hq0])
  have hlog1 : Real.log (endpointPreciseArgument t : ℝ) ≤ 4 := by
    have hb := Real.log_le_log (by linarith only [hq0] : 0 < (endpointPreciseArgument t : ℝ)) hq1
    have h16 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
      have h16' := Real.log_pow (2 : ℝ) 4
      norm_num only at h16'
      exact h16'
    linarith only [hb, h16, Real.log_two_lt_d9]
  have hh := abs_le.mp hc.2.2
  have hl : -(1 : ℝ) ≤ endpointPrecisePhaseLog t := by linarith only [hh.2, hlog0]
  have hu : (endpointPrecisePhaseLog t : ℝ) ≤ 5 := by linarith only [hh.1, hlog1]
  have hp0 : (0 : ℝ) ≤ endpointPi := by
    norm_num only [endpointPi, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat]
  have hp1 : (endpointPi : ℝ) ≤ 4 := by
    norm_num only [endpointPi, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat]
  have hm1 := mul_nonneg ht0R (sub_nonneg.mpr hu)
  have hm2 := mul_nonneg ht0R (sub_nonneg.mpr hl)
  rw [abs_le]
  norm_num only [endpointPreciseTheta, Rat.cast_sub, Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat]
  constructor <;> nlinarith only [ht0R, htR, hl, hu, hp0, hp1, hm1, hm2]

/-- If the phase logarithm check succeeds for `0 ≤ t ≤ 100`, the rounded complex exponential
approximates the elementary phase factor within `1/500000000`. The proof combines phase
stability with rounded-squaring error. -/
theorem norm_endpoint_precise_factor (t : ℚ) (ht0 : 0 ≤ t) (ht : t ≤ 100)
    (hcheck : endpointPrecisePhaseCheck t = true) :
    ‖Complex.exp ((backlundThetaMain t : ℂ) * Complex.I) -
          Analysis.rationalComplexCast
            (Analysis.rationalScaledPhase (10 ^ 15) (endpointPreciseTheta t) 16 11)‖ ≤
      1 / 500000000 := by
  have hθ := endpoint_precise_theta_error t ht0 ht hcheck
  have h1 := Analysis.norm_phase_exp_sub_le (backlundThetaMain t) (endpointPreciseTheta t)
  have h2 :=
    norm_endpoint_phase (endpointPreciseTheta t) (endpoint_precise_theta_range t ht0 ht hcheck)
  rw [← Complex.ofReal_ratCast] at h2
  have h :=
    norm_sub_le_norm_sub_add_norm_sub (Complex.exp (Complex.I * (backlundThetaMain t : ℂ)))
      (Complex.exp (Complex.I * (((endpointPreciseTheta t : ℝ) : ℂ))))
      (Analysis.rationalComplexCast
        (Analysis.rationalScaledPhase (10 ^ 15) (endpointPreciseTheta t) 16 11))
  rw [mul_comm]
  exact h.trans ((add_le_add (h1.trans hθ) h2).trans (by norm_num only))

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
