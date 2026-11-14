/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100FiniteBounds
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100PhasePrecise
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100FiniteMagnitude
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100NormalizedApprox

/-! # Error in the rotated rational approximation -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

private theorem norm_rotated_error (P Q E W : ℂ) (hP : ‖P‖ = 1) (hE : ‖E‖ ≤ 137)
    (hphase : ‖P - Q‖ ≤ (95 / 1000000000 : ℝ)) (hfin : ‖E - W‖ ≤ (7 / 100000 : ℝ)) :
    ‖P * E - Q * W‖ ≤ (84 / 1000000 : ℝ) := by
  have hQ : ‖Q‖ ≤ 1 + (95 / 1000000000 : ℝ) := by
    have h := norm_le_norm_sub_add Q P
    rw [norm_sub_rev, hP] at h
    linarith only [hphase, h]
  have hm1 : ‖(P - Q) * E‖ ≤ (95 / 1000000000 : ℝ) * 137 := by
    rw [norm_mul]
    exact mul_le_mul hphase hE (norm_nonneg _) (by norm_num only)
  have hm2 : ‖Q * (E - W)‖ ≤ (1 + (95 / 1000000000 : ℝ)) * (7 / 100000) := by
    rw [norm_mul]
    exact mul_le_mul hQ hfin (norm_nonneg _) (by norm_num only)
  have heq : P * E - Q * W = (P - Q) * E + Q * (E - W) := by ring
  rw [heq]
  have h := norm_add_le ((P - Q) * E) (Q * (E - W))
  linarith only [hm1, hm2, h]

private theorem norm_rotated_error_common (P Q E W : ℂ) (hP : ‖P‖ = 1) (hE : ‖E‖ ≤ 137)
    (hphase : ‖P - Q‖ ≤ (611 / 1000000000 : ℝ)) (hfin : ‖E - W‖ ≤ (7 / 100000 : ℝ)) :
    ‖P * E - Q * W‖ ≤ (155 / 1000000 : ℝ) := by
  have hQ : ‖Q‖ ≤ 1 + (611 / 1000000000 : ℝ) := by
    have h := norm_le_norm_sub_add Q P
    rw [norm_sub_rev, hP] at h
    linarith only [hphase, h]
  have hm1 : ‖(P - Q) * E‖ ≤ (611 / 1000000000 : ℝ) * 137 := by
    rw [norm_mul]
    exact mul_le_mul hphase hE (norm_nonneg _) (by norm_num only)
  have hm2 : ‖Q * (E - W)‖ ≤ (1 + (611 / 1000000000 : ℝ)) * (7 / 100000) := by
    rw [norm_mul]
    exact mul_le_mul hQ hfin (norm_nonneg _) (by norm_num only)
  have heq : P * E - Q * W = (P - Q) * E + Q * (E - W) := by ring
  rw [heq]
  have h := norm_add_le ((P - Q) * E) (Q * (E - W))
  linarith only [hm1, hm2, h]

/-- At `14 ≤ t ≤ 31`, successful common and narrow phase checks bound the real error of the
rotated rational approximation by `84/1000000`. The estimate combines the norm of the finite
Euler–Maclaurin approximation with phase and finite-sum errors. -/
theorem abs_endpoint_rotated_error (t : ℚ) (ht14 : 14 ≤ t) (ht31 : t ≤ 31)
    (hcheck : endpointPhaseLogCheck t = true) (hprecise : endpointPhasePreciseCheck t = true) :
    |normalizedFiniteEM8 t - ((endpointRotatedFinite t).1 : ℝ)| ≤ 84 / 1000000 := by
  have ht0 : 0 ≤ t := by linarith only [ht14]
  have ht100 : t ≤ 100 := by linarith only [ht31]
  have ht14R : (14 : ℝ) ≤ t := by exact_mod_cast ht14
  have ht100R : (t : ℝ) ≤ 100 := by exact_mod_cast ht100
  have hp := norm_endpoint_precise_phase t ht0 ht31 hcheck hprecise
  have he := norm_finiteEM8_le t ht14R ht100R
  have hf := norm_endpoint_finite_approx t ht14 ht100
  let P : ℂ := Complex.exp ((backlundThetaMain t : ℂ) * Complex.I)
  let Q : ℂ :=
    Analysis.rationalComplexCast (Analysis.rationalScaledPhase (10 ^ 15) (endpointTheta t) 16 11)
  let E : ℂ := finiteEM8 t
  let W : ℂ := Analysis.rationalComplexCast (endpointFiniteApprox t)
  have hn : ‖P‖ = 1 := Complex.norm_exp_ofReal_mul_I (backlundThetaMain t)
  have hb := norm_rotated_error P Q E W hn he hp hf
  have hr := Complex.abs_re_le_norm (P * E - Q * W)
  have h := hr.trans hb
  change |normalizedFiniteEM8 t - (Analysis.rationalComplexCast (endpointRotatedFinite t)).re| ≤ _
  simpa only [P, Q, E, W, normalizedFiniteEM8, endpointRotatedFinite,
    Analysis.rationalComplexCast_mul, Complex.sub_re] using h

/-- At `14 ≤ t ≤ 100`, a successful common phase check bounds the real error of the
rotated rational approximation by `155/1000000`. This common estimate applies throughout
the endpoint range without requiring the narrower logarithm check. -/
theorem abs_endpoint_rotated_common (t : ℚ) (ht14 : 14 ≤ t) (ht100 : t ≤ 100)
    (hcheck : endpointPhaseLogCheck t = true) :
    |normalizedFiniteEM8 t - ((endpointRotatedFinite t).1 : ℝ)| ≤ 155 / 1000000 := by
  have ht0 : 0 ≤ t := by linarith only [ht14]
  have ht14R : (14 : ℝ) ≤ t := by exact_mod_cast ht14
  have ht100R : (t : ℝ) ≤ 100 := by exact_mod_cast ht100
  have hp := norm_endpoint_phase_factor t ht0 ht100 hcheck
  have he := norm_finiteEM8_le t ht14R ht100R
  have hf := norm_endpoint_finite_approx t ht14 ht100
  let P : ℂ := Complex.exp ((backlundThetaMain t : ℂ) * Complex.I)
  let Q : ℂ :=
    Analysis.rationalComplexCast (Analysis.rationalScaledPhase (10 ^ 15) (endpointTheta t) 16 11)
  let E : ℂ := finiteEM8 t
  let W : ℂ := Analysis.rationalComplexCast (endpointFiniteApprox t)
  have hn : ‖P‖ = 1 := Complex.norm_exp_ofReal_mul_I (backlundThetaMain t)
  have hb := norm_rotated_error_common P Q E W hn he hp hf
  have hr := Complex.abs_re_le_norm (P * E - Q * W)
  have h := hr.trans hb
  change |normalizedFiniteEM8 t - (Analysis.rationalComplexCast (endpointRotatedFinite t)).re| ≤ _
  simpa only [P, Q, E, W, normalizedFiniteEM8, endpointRotatedFinite,
    Analysis.rationalComplexCast_mul, Complex.sub_re] using h

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
