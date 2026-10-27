/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ScaledGammaPhaseNodes
public import PseudoPrime.Analysis.RationalPhase64Checkpoint

/-! # A kernel-checked phase endpoint with rounded range reduction -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Claim: the scaled rational endpoint lower value exceeds 141/10^6 at the selected node.
Proof: compute a length-16 Taylor sum, seven rounded squares and the rounded Gamma coefficient.
Role: certify the same nontrivial endpoint using the uniformly bounded phase evaluator. -/
theorem phase64_scaled_node_at_scale64_check :
    decide
        ((141 / 1000000 : ℚ) ≤
          rationalScaledPhase64Lower (10 ^ 12) (109 / 50) (423097 / 20000) (1 / 100000)) =
      true := by
  decide +kernel

/-- Claim: the actual Gamma-resolvent gap at x=64 and t=109/50 is at least 1/10000.
Proof: combine the scaled rational check, the proved logarithmic enclosure and Gamma error.
Role: validate the low-degree endpoint route without claiming a complete spectral cover. -/
theorem phase64_actual_gap_at_scale64_of_scaled_node :
    (1 / 10000 : ℝ) ≤
      finiteSignedResolvent phaseResolvent64Coefficients (((109 / 50 : ℚ) : ℝ)) +
        (Complex.Gamma ((1 / 2 : ℂ) + Complex.I * ((109 / 50 : ℚ) : ℂ)) *
            (64 : ℂ) ^ (Complex.I * ((109 / 50 : ℚ) : ℂ))).re := by
  have hc :
    (141 / 1000000 : ℚ) ≤
      rationalScaledPhase64Lower (10 ^ 12) (109 / 50) (423097 / 20000) (1 / 100000) :=
    of_decide_eq_true phase64_scaled_node_at_scale64_check
  have hr := (Rat.cast_le (K := ℝ)).mpr hc
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hr
  apply
    phase64_actual_gap_ge_of_rounded_node (by norm_num only : (0 : ℝ) < 64)
      (by norm_num only : 0 < 10 ^ 12) (109 / 50)
      (by norm_num only [Rat.cast_div, Rat.cast_ofNat, abs_of_pos])
  have h :=
    rationalScaledPhase64Lower_le (x := 64) (10 ^ 12) (109 / 50) (423097 / 20000) (1 / 100000)
      (by norm_num only [Rat.cast_div, Rat.cast_ofNat, abs_of_pos]) phase64_scale64_phase_enclosure
  have hb :
    (1 / 10000 : ℝ) + (1 / 25000 + 32768 / ((10 ^ 12 : ℕ) : ℝ)) ≤
      (rationalScaledPhase64Lower (10 ^ 12) (109 / 50) (423097 / 20000) (1 / 100000) : ℝ) := by
    norm_num only
    linarith only [hr]
  exact hb.trans h

end PseudoPrime.Analysis
