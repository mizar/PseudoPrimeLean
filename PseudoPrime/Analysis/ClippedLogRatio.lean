/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.LogWeightedVariation

/-! # Clipped logarithmic ratios and integrals -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The logarithmic atom log(max(v,u)/v). For v>0 it equals zero below v
and log(u/v) above v, and is continuous at the join. This permits finite
summation under integrals without a moving lower endpoint. -/
noncomputable def positiveLogRatio (v u : ℝ) : ℝ :=
  Real.log (max v u / v)

/-- Below v, the clipped logarithmic atom is zero. Use max(v,u)=v and
log(v/v)=0. This removes terms above each arithmetic cutoff. -/
theorem positiveLogRatio_zero {v u : ℝ} (hu : u ≤ v) : positiveLogRatio v u = 0 := by
  rw [positiveLogRatio, max_eq_left hu, Real.log_div_self]

/-- At or above v, the clipped logarithmic atom is log(u/v).
Use max(v,u)=u. This identifies the ordinary logarithmic weight on its support. -/
theorem positiveLogRatio_eq_log {v u : ℝ} (hu : v ≤ u) :
    positiveLogRatio v u = Real.log (u / v) := by rw [positiveLogRatio, max_eq_right hu]

/-- For positive v, the clipped logarithmic atom is continuous on the real line.
The max numerator stays positive, so division and logarithm preserve continuity.
This supplies integrability for the finite interchange of sum and integral. -/
theorem positiveLogRatio_continuous {v : ℝ} (hv : 0 < v) : Continuous (positiveLogRatio v) := by
  apply ((continuous_const.max continuous_id).div_const v).log
  intro u
  exact (div_pos (hv.trans_le (le_max_left v u)) hv).ne'

/-- If a<=b<=v, the clipped logarithm times any density has zero interval
integral. The logarithmic factor vanishes at every point.
This removes the part below an atom's support. -/
theorem clipped_integral_zero {v a b : ℝ} (hab : a ≤ b) (hb : b ≤ v) (Q : ℝ → ℝ) :
    (∫ u in a..b, positiveLogRatio v u * Q u) = 0 := by
  rw [← intervalIntegral.integral_zero (a := a) (b := b)]
  apply intervalIntegral.integral_congr
  intro u hu
  rw [Set.uIcc_of_le hab] at hu
  dsimp only
  rw [positiveLogRatio_zero (hu.2.trans hb), zero_mul]

/-- If v<=a<=b, the clipped and ordinary logarithmic integrals agree.
Replace the clipped logarithm pointwise on the closed interval.
This reduces supported atoms to the smooth variation identity. -/
theorem clipped_integral_eq_log {v a b : ℝ} (hab : a ≤ b) (ha : v ≤ a) (Q : ℝ → ℝ) :
    (∫ u in a..b, positiveLogRatio v u * Q u) = ∫ u in a..b, Real.log (u / v) * Q u := by
  apply intervalIntegral.integral_congr
  intro u hu
  rw [Set.uIcc_of_le hab] at hu
  dsimp only
  rw [positiveLogRatio_eq_log (ha.trans hu.1)]

/-- For positive v between a and b and a continuous density Q, the clipped
logarithmic integral on [a,b] equals the ordinary one on [v,b]. Split at v,
use the zero lower piece, and identify the upper piece.
This aligns the fixed integration intervals with each positive atom. -/
theorem clipped_integral_from_join {v a b : ℝ} (hv : 0 < v) (ha : a ≤ v) (hb : v ≤ b) {Q : ℝ → ℝ}
    (hQ : Continuous Q) :
    (∫ u in a..b, positiveLogRatio v u * Q u) = ∫ u in v..b, Real.log (u / v) * Q u := by
  have hc : Continuous (fun u ↦ positiveLogRatio v u * Q u) :=
    (positiveLogRatio_continuous hv).mul hQ
  rw [←
    intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable a v)
      (hc.intervalIntegrable v b)]
  rw [clipped_integral_zero ha le_rfl, clipped_integral_eq_log hb le_rfl, zero_add]

end PseudoPrime.Analysis
