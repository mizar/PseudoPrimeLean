/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.InverseMellin
public import Mathlib.Tactic.Ring

/-! # Elementary rules for inverse Mellin integrals -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The project and mathlib inverse Mellin conventions agree for complex-valued F.
Commute the two integrand factors and identify real scalar multiplication. This
allows reuse of mathlib inversion for the higher logarithmic weight transforms. -/
theorem inverseMellin_eq_mellinInv (F : ℂ → ℂ) (σ u : ℝ) :
    inverseMellin F σ u = mellinInv σ F u := by
  unfold inverseMellin mellinInv
  rw [Complex.real_smul]
  congr 1
  apply MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall fun t ↦ by
    dsimp only
    rw [mul_comm (t : ℂ) Complex.I, smul_eq_mul]
    exact mul_comm _ _

/-- Multiplying a complex kernel by A multiplies its inverse Mellin transform by A.
Pull the constant through the Bochner integral and commute scalar factors. This
linear identity has no integrability premise and normalizes rational kernel powers. -/
theorem inverseMellin_const_mul (F : ℂ → ℂ) (A : ℂ) (σ u : ℝ) :
    inverseMellin (fun z ↦ A * F z) σ u = A * inverseMellin F σ u := by
  have he (t : ℝ) : A * F ((σ : ℂ) + Complex.I * t) *
      (u : ℂ) ^ (-((σ : ℂ) + Complex.I * t)) =
      A * (F ((σ : ℂ) + Complex.I * t) * (u : ℂ) ^ (-((σ : ℂ) + Complex.I * t))) :=
    mul_assoc _ _ _
  unfold inverseMellin
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall he),
    MeasureTheory.integral_const_mul]
  ring

/-- For positive u, multiplication by exp(Az) changes the inverse power base to
u exp(-A). Expand complex powers with real logarithms and combine exponentials.
This scalar identity implements the upper support translation in Mellin inversion. -/
theorem exp_mul_inverseMellin_power (A : ℝ) {u : ℝ} (hu : 0 < u) (z : ℂ) :
    Complex.exp ((A : ℂ) * z) * (u : ℂ) ^ (-z) =
      ((u * Real.exp (-A) : ℝ) : ℂ) ^ (-z) := by
  have hp := mul_pos hu (Real.exp_pos (-A))
  have hl : Real.log (u * Real.exp (-A)) = Real.log u - A := by
    rw [Real.log_mul hu.ne' (Real.exp_ne_zero _), Real.log_exp]
    exact rfl
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hu.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hp.ne'),
    ← Complex.ofReal_log hu.le, ← Complex.ofReal_log hp.le, ← Complex.exp_add, hl,
    Complex.ofReal_sub]
  congr 1
  ring

/-- Multiplying a kernel by exp(Az) replaces the positive inverse-Mellin argument
u by u exp(-A). Apply the scalar power identity pointwise in the vertical integral.
This shifts the support cutoff while preserving integration-line independence. -/
theorem inverseMellin_exp_mul (F : ℂ → ℂ) (A σ : ℝ) {u : ℝ} (hu : 0 < u) :
    inverseMellin (fun z ↦ Complex.exp ((A : ℂ) * z) * F z) σ u =
      inverseMellin F σ (u * Real.exp (-A)) := by
  unfold inverseMellin
  congr 1
  apply MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall fun t ↦ by
    dsimp only
    rw [mul_right_comm, exp_mul_inverseMellin_power A hu]
    exact mul_comm _ _

end PseudoPrime.Analysis
