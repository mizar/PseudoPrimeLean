/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.RationalGammaPhaseNodes
public import PseudoPrime.Analysis.LogTaylorBounds

/-! # Logarithmic interval certificates on continuous scales -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Input: two rational logarithm interval certificates and any real point between their arguments.
Claim: the certified outer endpoints enclose the logarithm of every point in that interval.
Proof: recover positivity and use monotonicity of the real logarithm.
Role: reuse endpoint certificates on a continuous scale interval. -/
theorem log_enclosure_on_rational_interval {y : ℝ} {a b l u la ua : ℚ} {ja na jb nb : ℕ}
    (hA : rationalLogIntervalCheck a ja na l ua = true)
    (hB : rationalLogIntervalCheck b jb nb la u = true) (ha : (a : ℝ) ≤ y) (hb : y ≤ (b : ℝ)) :
    (l : ℝ) ≤ Real.log y ∧ Real.log y ≤ (u : ℝ) := by
  have haQ : 0 < a := (of_decide_eq_true hA).1
  have ha0 : 0 < (a : ℝ) := Rat.cast_pos.mpr haQ
  have hy0 : 0 < y := ha0.trans_le ha
  exact
    ⟨(rationalLogIntervalCheck_sound hA).1.trans (Real.log_le_log ha0 ha),
      (Real.log_le_log hy0 hb).trans (rationalLogIntervalCheck_sound hB).2⟩

/-- Input: a rational enclosure of log(256*x) and a rational ordinate of either sign.
Claim: the midpoint phase has uncertainty |t| times half the enclosure width.
Proof: apply the real midpoint bound and commute rational casts.
Role: supply one continuous logarithmic enclosure to all finite phase node checks. -/
theorem phase_enclosure_of_rational_log_interval {x : ℝ} {l u : ℚ}
    (hl : (l : ℝ) ≤ Real.log (256 * x)) (hu : Real.log (256 * x) ≤ (u : ℝ)) (t : ℚ) :
    |(t : ℝ) * Real.log (256 * x) - ((t * ((l + u) / 2) : ℚ) : ℝ)| ≤
      ((|t| * ((u - l) / 2) : ℚ) : ℝ) := by
  have h := phase_center_error_of_log_enclosure hl hu (t : ℝ)
  simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_add, Rat.cast_sub, Rat.cast_abs,
    Rat.cast_ofNat] using h

end PseudoPrime.Analysis
