/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.TriangularCutoffMangoldt

/-! # Explicit alpha-18 cutoff main term -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For positive input, differentiate the explicit primitive of the cutoff
Abel main-term integrand. Power addition reduces the exponents. -/
theorem triangular18_cutoff_main_deriv {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun z : ℝ ↦ z ^ (1 / 2 : ℝ) * (-32 - Real.log z))
      (u ^ (-3 / 2 : ℝ) * (1 - (36 + Real.log u) / 2) * u) u := by
  have h :=
    (Real.hasDerivAt_rpow_const (p := 1 / 2) (Or.inl hu.ne')).mul
      ((Real.hasDerivAt_log hu.ne').const_sub (-32))
  have hp : u ^ (1 / 2 : ℝ) = u ^ (-1 / 2 : ℝ) * u := by
    have e := Real.rpow_add hu (-1 / 2) 1
    norm_num only [Real.rpow_one] at e
    simpa only [neg_div] using e
  have hm : u ^ (-1 / 2 : ℝ) = u ^ (-3 / 2 : ℝ) * u := by
    have e := Real.rpow_add hu (-3 / 2) 1
    norm_num only [Real.rpow_one] at e
    simpa only [neg_div] using e
  apply h.congr_deriv
  norm_num only
  rw [hp]
  field_simp [hu.ne']
  simp only [neg_div] at hm
  rw [hm]
  ring

/-- The cutoff derivative main-term integral equals -32 minus 4 exp(-18).
Apply the fundamental theorem on the positive support interval. -/
theorem triangular18_cutoff_main_integral :
    (∫ u in Real.exp (-36)..(1 : ℝ), u ^ (-3 / 2 : ℝ) * (1 - (36 + Real.log u) / 2) * u) =
      -32 - 4 * Real.exp (-18) := by
  have hab : Real.exp (-36 : ℝ) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num only)
  have hc :
    ContinuousOn (fun u : ℝ ↦ u ^ (-3 / 2 : ℝ) * (1 - (36 + Real.log u) / 2) * u)
      (Set.uIcc (Real.exp (-36)) 1) := by
    rw [Set.uIcc_of_le hab]
    intro u hu
    have hp := lt_of_lt_of_le (Real.exp_pos (-36)) hu.1
    exact
      (((Real.continuousAt_rpow_const u (-3 / 2) (Or.inl hp.ne')).mul
              (continuousAt_const.sub
                ((continuousAt_const.add (Real.continuousAt_log hp.ne')).div_const 2))).mul
          continuousAt_id).continuousWithinAt
  have h :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun u hu ↦
        triangular18_cutoff_main_deriv
          (by
            rw [Set.uIcc_of_le hab] at hu
            exact lt_of_lt_of_le (Real.exp_pos (-36)) hu.1))
      hc.intervalIntegrable
  rw [Real.one_rpow, Real.log_one, Real.log_exp, ← Real.exp_mul] at h
  norm_num only [one_mul, sub_zero] at h
  simpa only [neg_div, mul_comm] using h

/-- At positive scale, the Abel main term equals x times (68 + 4 exp(-18)).
A linear substitution transfers the exact cutoff integral to the scaled interval. -/
theorem triangular18_cutoff_abel_main_term {x : ℝ} (hx : 0 < x) :
    36 * x -
        (∫ t in (Real.exp (-36) * x)..x,
          (((t / x) ^ (-3 / 2 : ℝ) * (1 - (36 + Real.log (t / x)) / 2)) / x) * t) =
      x * (68 + 4 * Real.exp (-18)) := by
  let g := fun u : ℝ ↦ u ^ (-3 / 2 : ℝ) * (1 - (36 + Real.log u) / 2) * u
  have he (t : ℝ) :
    (((t / x) ^ (-3 / 2 : ℝ) * (1 - (36 + Real.log (t / x)) / 2)) / x) * t = g (t / x) := by
    dsimp only [g]
    ring
  have hi :
    (∫ t in (Real.exp (-36) * x)..x,
        (((t / x) ^ (-3 / 2 : ℝ) * (1 - (36 + Real.log (t / x)) / 2)) / x) * t) =
      x * (-32 - 4 * Real.exp (-18)) := by
    rw [intervalIntegral.integral_congr (fun t _ ↦ he t),
      intervalIntegral.integral_comp_div g hx.ne', mul_div_cancel_right₀ _ hx.ne', div_self hx.ne',
      smul_eq_mul]
    exact congrArg (fun z : ℝ ↦ x * z) triangular18_cutoff_main_integral
  rw [hi]
  ring

end PseudoPrime.Analysis
