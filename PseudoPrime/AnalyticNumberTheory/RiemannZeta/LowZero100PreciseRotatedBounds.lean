/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100PreciseFiniteBounds
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100PrecisePhaseBounds
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100FiniteMagnitude
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100NormalizedApprox

/-! # Error in the precise rotated rational approximation -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

private theorem norm_precise_rotated_error (P Q E W : ℂ) (hP : ‖P‖ = 1) (hE : ‖E‖ ≤ 137)
    (hphase : ‖P - Q‖ ≤ (1 / 500000000 : ℝ)) (hfin : ‖E - W‖ ≤ (1 / 2000000 : ℝ)) :
    ‖P * E - Q * W‖ ≤ (1 / 1000000 : ℝ) := by
  have hQ : ‖Q‖ ≤ 1 + (1 / 500000000 : ℝ) := by
    have h := norm_le_norm_sub_add Q P
    rw [norm_sub_rev, hP] at h
    linarith only [hphase, h]
  have hm1 : ‖(P - Q) * E‖ ≤ (1 / 500000000 : ℝ) * 137 := by
    rw [norm_mul]
    exact mul_le_mul hphase hE (norm_nonneg _) (by norm_num only)
  have hm2 : ‖Q * (E - W)‖ ≤ (1 + (1 / 500000000 : ℝ)) * (1 / 2000000) := by
    rw [norm_mul]
    exact mul_le_mul hQ hfin (norm_nonneg _) (by norm_num only)
  have heq : P * E - Q * W = (P - Q) * E + Q * (E - W) := by ring
  rw [heq]
  have h := norm_add_le ((P - Q) * E) (Q * (E - W))
  linarith only [hm1, hm2, h]

/-- At `14 ≤ t ≤ 100`, a successful precise phase check bounds the real error of the rotated
rational finite approximation by `1/1000000`. The proof combines the high-precision phase
and power-term estimates with the uniform magnitude bound. -/
theorem abs_endpoint_precise_rotated (t : ℚ) (ht14 : 14 ≤ t) (ht100 : t ≤ 100)
    (hcheck : endpointPrecisePhaseCheck t = true) :
    |normalizedFiniteEM8 t - ((endpointPreciseRotated t).1 : ℝ)| ≤ 1 / 1000000 := by
  have ht0 : 0 ≤ t := by linarith only [ht14]
  have ht14R : (14 : ℝ) ≤ t := by exact_mod_cast ht14
  have ht100R : (t : ℝ) ≤ 100 := by exact_mod_cast ht100
  have hp := norm_endpoint_precise_factor t ht0 ht100 hcheck
  have he := norm_finiteEM8_le t ht14R ht100R
  have hf := norm_endpoint_precise_finite t ht14 ht100
  let P : ℂ := Complex.exp ((backlundThetaMain t : ℂ) * Complex.I)
  let Q : ℂ :=
    Analysis.rationalComplexCast
      (Analysis.rationalScaledPhase (10 ^ 15) (endpointPreciseTheta t) 16 11)
  let E : ℂ := finiteEM8 t
  let W : ℂ := Analysis.rationalComplexCast (endpointPreciseFinite t)
  have hn : ‖P‖ = 1 := Complex.norm_exp_ofReal_mul_I (backlundThetaMain t)
  have hb := norm_precise_rotated_error P Q E W hn he hp hf
  have hr := Complex.abs_re_le_norm (P * E - Q * W)
  have h := hr.trans hb
  change |normalizedFiniteEM8 t - (Analysis.rationalComplexCast (endpointPreciseRotated t)).re| ≤ _
  simpa only [P, Q, E, W, normalizedFiniteEM8, endpointPreciseRotated,
    Analysis.rationalComplexCast_mul, Complex.sub_re] using h

/-- At `14 ≤ t ≤ 100`, a successful precise phase check bounds the distance from normalized
zeta to the rotated rational approximation by `3/2500000`. This includes both the analytic
Euler–Maclaurin remainder and the rational calculation error. -/
theorem abs_endpoint_precise_zeta (t : ℚ) (ht14 : 14 ≤ t) (ht100 : t ≤ 100)
    (hcheck : endpointPrecisePhaseCheck t = true) :
    |RiemannXi.normalizedZeta t - ((endpointPreciseRotated t).1 : ℝ)| ≤ 3 / 2500000 := by
  have ht0 : (0 : ℝ) ≤ t := by
    have h : (14 : ℝ) ≤ t := by exact_mod_cast ht14
    linarith only [h]
  have htR : (t : ℝ) ≤ 100 := by exact_mod_cast ht100
  have h1 := abs_normalized_zeta_sub_em8_le t ht0 htR
  have h2 := abs_endpoint_precise_rotated t ht14 ht100 hcheck
  have h :=
    abs_sub_le (RiemannXi.normalizedZeta t) (normalizedFiniteEM8 t)
      ((endpointPreciseRotated t).1 : ℝ)
  linarith only [h1, h2, h]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
