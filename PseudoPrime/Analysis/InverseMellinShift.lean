/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.InverseMellin
public import Mathlib.Tactic.Ring

/-! # Translation of inverse Mellin integrals -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Input: a complex function, real shifts and a positive argument.
Claim: translation of the kernel multiplies its inverse by the corresponding real-base power.
Proof: split the complex power and pull the constant through the integral.
Role: reuse scalar inversion formulas for shifted rational kernels. -/
theorem inverseMellin_shift (F : ℂ → ℂ) (a c : ℝ) {u : ℝ} (hu : 0 < u) :
    inverseMellin (fun s ↦ F (s + a)) c u =
      (u : ℂ) ^ (a : ℂ) * inverseMellin F (c + a) u := by
  have he (t : ℝ) :
    F (((c : ℂ) + Complex.I * t) + a) * (u : ℂ) ^ (-((c : ℂ) + Complex.I * t)) =
      (u : ℂ) ^ (a : ℂ) *
        (F (((c + a : ℝ) : ℂ) + Complex.I * t) *
          (u : ℂ) ^ (-(((c + a : ℝ) : ℂ) + Complex.I * t))) := by
    rw [Complex.ofReal_add]
    have hs : (c : ℂ) + Complex.I * t + a = (c : ℂ) + a + Complex.I * t := by ring
    rw [hs]
    have hp : -(↑c + Complex.I * ↑t) = (a : ℂ) + -(↑c + ↑a + Complex.I * ↑t) := by ring
    rw [hp, Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hu.ne')]
    ring
  unfold inverseMellin
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall he),
    MeasureTheory.integral_const_mul]
  ring

end PseudoPrime.Analysis
