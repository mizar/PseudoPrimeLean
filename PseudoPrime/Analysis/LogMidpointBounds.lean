/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith

/-! # Interval bounds for a backward logarithmic midpoint -/

public section

namespace PseudoPrime.Analysis

/-- For L in [a,b] and delta in [d,e] with e<2, the shifted midpoint
L+log(1-delta/2) lies between a+1-(1-e/2)^{-1} and b-d/2.
The reciprocal and ordinary tangent inequalities for log give both endpoints.
Cell certificates can substitute rational bounds without evaluating log again. -/
theorem backward_phase_bounds {L a b δ d e : ℝ} (hL : L ∈ Set.Icc a b) (hd : δ ∈ Set.Icc d e)
    (he : e < 2) :
    a + 1 - (1 - e / 2)⁻¹ ≤ L + Real.log (1 - δ / 2) ∧ L + Real.log (1 - δ / 2) ≤ b - d / 2 := by
  have hp : 0 < 1 - δ / 2 := by linarith only [hd.2, he]
  have hi :=
    one_div_le_one_div_of_le (show 0 < 1 - e / 2 by linarith only [he])
      (show 1 - e / 2 ≤ 1 - δ / 2 by linarith only [hd.2])
  simp only [one_div] at hi
  have hl := Real.one_sub_inv_le_log_of_pos hp
  have hu := Real.log_le_sub_one_of_pos hp
  constructor <;> linarith only [hL.1, hL.2, hd.1, hi, hl, hu]

end PseudoPrime.Analysis
