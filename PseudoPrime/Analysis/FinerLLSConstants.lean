/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ParameterizedReciprocalLowerBound

/-! # Refined Euler, zero-mass and reciprocal constants for LLS -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Claim: the Euler constant is at most 0.57722.
Proof: combine the exact harmonic sum H_128 with the certified lower bound for log(128.5)
and the monotone midpoint approximation. Role: sharpen LLS reciprocal and zero-mass costs. -/
theorem eulerMascheroniConstant_le_28861_div_50000 :
    Real.eulerMascheroniConstant ≤ (28861 / 50000 : ℝ) := by
  have hh :
    harmonic 128 =
      (72552921080947538317446905633815133414572988188576608701 /
          13353756090997411579403749204440236542538872688049072000 :
        ℚ) := by
    decide +kernel
  have hc :
    rationalLogIntervalCheck (257 / 2) 7 12 (485592890 / 100000000) (485592891 / 100000000) =
      true := by
    decide +kernel
  have hl := (rationalLogIntervalCheck_sound hc).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hl
  have hg := eulerMascheroniConstant_le_midpoint 127
  norm_num only [midpointEulerSequence, hh, Rat.cast_div, Rat.cast_ofNat, Nat.reduceAdd,
    Nat.cast_ofNat] at hg
  linarith only [hl, hg]

end PseudoPrime.Analysis
