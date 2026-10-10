/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Analysis.Complex.Exponential

/-! A real-part minimum principle on the closed unit disk for entire functions. -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- An entire function whose real part is bounded below on the unit circle has the same
lower bound on the closed unit disk. Apply the maximum modulus principle to its negative
exponential and use strict monotonicity of the real exponential. This extends finite
prime-power comparisons from unit roots to all Ramanujan roots. -/
theorem lower_re_on_unitDisk {g : ℂ → ℂ} (hg : Differentiable ℂ g) {b : ℝ}
    (hb : ∀ z : ℂ, ‖z‖ = 1 → b ≤ (g z).re) {z : ℂ} (hz : ‖z‖ ≤ 1) : b ≤ (g z).re := by
  have hd : Differentiable ℂ (fun w ↦ Complex.exp (-(g w))) :=
    Complex.differentiable_exp.comp hg.neg
  have hc : ∀ w ∈ frontier (Metric.ball (0 : ℂ) 1), ‖Complex.exp (-(g w))‖ ≤ Real.exp (-b) := by
    intro w hw
    rw [frontier_ball (0 : ℂ) (by norm_num only : (1 : ℝ) ≠ 0)] at hw
    have hw1 : ‖w‖ = 1 := by simpa only [mem_sphere_iff_norm, sub_zero] using hw
    rw [Complex.norm_exp, Complex.neg_re]
    exact Real.exp_le_exp.mpr (neg_le_neg (hb w hw1))
  have hzB : z ∈ closure (Metric.ball (0 : ℂ) 1) := by
    rw [closure_ball (0 : ℂ) (by norm_num only : (1 : ℝ) ≠ 0)]
    simpa only [mem_closedBall_iff_norm, sub_zero] using hz
  have h :=
    Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hd.diffContOnCl hc hzB
  rw [Complex.norm_exp, Complex.neg_re, Real.exp_le_exp] at h
  exact neg_le_neg_iff.mp h

end PseudoPrime.Analysis
