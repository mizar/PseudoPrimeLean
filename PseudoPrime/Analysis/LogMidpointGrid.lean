/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.LogMidpointBounds
public import PseudoPrime.Analysis.IntegerIntervalComputed
import Mathlib.Tactic.Linarith

/-! # Shared midpoint bounds for translated logarithmic cells -/

public section

namespace PseudoPrime.Analysis

/-- Endpoint exponential bounds and rational cross-product inequalities bound
the quarter-width throughout a real block. The result supplies the shared
relative-width interval used by translated logarithmic cells. -/
theorem quarter_width_block {L a b E U d e : ℝ} (hL : L ∈ Set.Icc a b) (hE : E ≤ Real.exp (a / 2))
    (hU : Real.exp (b / 2) ≤ U) (hd : 0 ≤ d) (he : 0 ≤ e) (hl : 4 * d * U ≤ a)
    (hu : b ≤ 4 * e * E) : L / 4 * Real.exp (-L / 2) ∈ Set.Icc d e := by
  have hEL : E ≤ Real.exp (L / 2) := hE.trans (Real.exp_le_exp.mpr (by linarith only [hL.1]))
  have hUL := (Real.exp_le_exp.mpr (show L / 2 ≤ b / 2 by linarith only [hL.2])).trans hU
  have hdm := mul_le_mul_of_nonneg_left hUL hd
  have hem := mul_le_mul_of_nonneg_left hEL he
  rw [neg_div, Real.exp_neg, ← div_eq_mul_inv]
  constructor
  · apply (le_div_iff₀ (Real.exp_pos _)).mpr
    nlinarith only [hdm, hl, hL.1]
  · apply (div_le_iff₀ (Real.exp_pos _)).mpr
    nlinarith only [hem, hu, hL.2]

/-- A translated cell and a shared relative-width interval bound the backward
logarithmic phase after subtracting the translation. Both endpoints follow
from the reciprocal and ordinary tangent bounds for the logarithm. -/
theorem backward_phase_translate {L a b t δ d e : ℝ} (hL : L ∈ Set.Icc (a + t) (b + t))
    (hd : δ ∈ Set.Icc d e) (he : e < 2) :
    L + Real.log (1 - δ / 2) - t ∈ Set.Icc (a + 1 - (1 - e / 2)⁻¹) (b - d / 2) := by
  have h := backward_phase_bounds hL hd he
  constructor <;> linarith only [h.1, h.2]

/-- Shared phase endpoint bounds and an interval containing the translation
enclose the true backward phase in the sum of two integer intervals.
This connects finite phase-center calculations to actual logarithmic cells. -/
theorem backward_phase_box {G : ℤ} {I J : IntegerInterval} {L a b t δ d e : ℝ}
    (hL : L ∈ Set.Icc (a + t) (b + t)) (hd : δ ∈ Set.Icc d e) (he : e < 2)
    (hl : (I.lower : ℝ) / G ≤ a + 1 - (1 - e / 2)⁻¹) (hu : b - d / 2 ≤ (I.upper : ℝ) / G)
    (ht : J.Contains G t) : (I.add J).Contains G (L + Real.log (1 - δ / 2)) := by
  have hb := backward_phase_translate hL hd he
  have hc : I.Contains G (L + Real.log (1 - δ / 2) - t) := ⟨hl.trans hb.1, hb.2.trans hu⟩
  simpa only [sub_add_cancel] using IntegerInterval.add_contains hc ht

end PseudoPrime.Analysis
