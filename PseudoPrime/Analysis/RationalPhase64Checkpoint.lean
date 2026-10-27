/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.RationalGammaPhaseNodes
public import PseudoPrime.Analysis.LogTaylorBounds

/-! # A kernel-checked Gamma phase endpoint at scale 64 -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Claim: the rational lower candidate at scale64's selected phase center exceeds 141/10^6.
Proof: evaluate the order-80 Taylor sum and order-256 rounded product in the kernel.
Role: check the executable endpoint evaluator against a nontrivial spectral node. -/
theorem phase64_rational_node_at_scale64_check :
    decide
        ((141 / 1000000 : ℚ) ≤
          rationalPhase64NodeLower (10 ^ 12) 80 (109 / 50) (423097 / 20000) (1 / 100000)) =
      true := by
  decide +kernel

/-- Claim: at t=109/50 and x=64 the actual phase is within 1/100000 of 423097/20000.
Proof: certify log(16384) by a rational logarithm interval and multiply its endpoints.
Role: discharge the transcendental premise of the representative node theorem. -/
theorem phase64_scale64_phase_enclosure :
    |((109 / 50 : ℚ) : ℝ) * Real.log (256 * (64 : ℝ)) - ((423097 / 20000 : ℚ) : ℝ)| ≤
      ((1 / 100000 : ℚ) : ℝ) := by
  have hc :
    rationalLogIntervalCheck 16384 14 14 (970406052 / 100000000) (970406054 / 100000000) =
      true := by
    decide +kernel
  obtain ⟨hl, hu⟩ := rationalLogIntervalCheck_sound hc
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hl hu ⊢
  exact abs_le.mpr ⟨by linarith only [hl, hu], by linarith only [hl, hu]⟩

/-- Claim: the actual Gamma-resolvent gap at x=64 and t=109/50 is at least 1/10000.
Proof: combine the kernel-checked rational gap, logarithmic enclosure and Gamma error budget.
Role: validate the complete endpoint route without asserting a continuous cover. -/
theorem phase64_actual_gap_at_scale64_node :
    (1 / 10000 : ℝ) ≤
      finiteSignedResolvent phaseResolvent64Coefficients (((109 / 50 : ℚ) : ℝ)) +
        (Complex.Gamma ((1 / 2 : ℂ) + Complex.I * ((109 / 50 : ℚ) : ℂ)) *
            (64 : ℂ) ^ (Complex.I * ((109 / 50 : ℚ) : ℂ))).re := by
  have hc :
    (141 / 1000000 : ℚ) ≤
      rationalPhase64NodeLower (10 ^ 12) 80 (109 / 50) (423097 / 20000) (1 / 100000) :=
    of_decide_eq_true phase64_rational_node_at_scale64_check
  have hr := (Rat.cast_le (K := ℝ)).mpr hc
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hr
  apply
    phase64_actual_gap_ge_of_rational_node (by norm_num only : (0 : ℝ) < 64)
      (by norm_num only : 0 < 10 ^ 12) 80 (109 / 50) (423097 / 20000) (1 / 100000)
      (by norm_num only [Rat.cast_div, Rat.cast_ofNat, abs_of_pos])
      (by norm_num only [Rat.cast_div, Rat.cast_ofNat, abs_of_pos]) phase64_scale64_phase_enclosure
  linarith only [hr]

end PseudoPrime.Analysis
