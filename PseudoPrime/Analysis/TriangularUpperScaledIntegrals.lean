/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.TriangularUpperMangoldt

/-! # Scaled alpha-18 upper-support main and error integrals -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For positive scale, the upper derivative variation integral equals
x^(3/4) times (12 exp 9 - 84). Linear substitution retains the exact budget. -/
theorem triangular18_upper_scaled_variation_integral {x : ℝ} (hx : 0 < x) :
    (∫ t in x..(Real.exp 36 * x),
        |((t / x) ^ (-3 / 2 : ℝ) * (Real.log (t / x) / 2 - 19)) / x| * t ^ (3 / 4 : ℝ)) =
      x ^ (3 / 4 : ℝ) * (12 * Real.exp 9 - 84) := by
  let g := fun u : ℝ ↦ |u ^ (-3 / 2 : ℝ) * (Real.log u / 2 - 19)| * u ^ (3 / 4 : ℝ)
  have he (t : ℝ) (ht : t ∈ Set.uIcc x (Real.exp 36 * x)) :
    |((t / x) ^ (-3 / 2 : ℝ) * (Real.log (t / x) / 2 - 19)) / x| * t ^ (3 / 4 : ℝ) =
      (x ^ (3 / 4 : ℝ) / x) * g (t / x) := by
    have he0 : (1 : ℝ) ≤ Real.exp 36 := Real.one_le_exp_iff.mpr (by norm_num only)
    have hab : x ≤ Real.exp 36 * x :=
      (one_mul x).symm.trans_le (mul_le_mul_of_nonneg_right he0 hx.le)
    rw [Set.uIcc_of_le hab] at ht
    have ht0 : 0 ≤ t := hx.le.trans ht.1
    have hp := Real.div_rpow ht0 hx.le (3 / 4)
    rw [abs_div, abs_of_pos hx]
    dsimp only [g]
    rw [hp]
    field_simp [hx.ne', (Real.rpow_pos_of_pos hx (3 / 4)).ne']
  rw [intervalIntegral.integral_congr he, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_div g hx.ne', mul_div_cancel_right₀ _ hx.ne', div_self hx.ne',
    smul_eq_mul]
  change
    (x ^ (3 / 4 : ℝ) / x) *
        (x *
          (∫ u in (1 : ℝ)..Real.exp 36,
            |u ^ (-3 / 2 : ℝ) * (Real.log u / 2 - 19)| * u ^ (3 / 4 : ℝ))) =
      _
  rw [triangular18_upper_variation_integral, ← mul_assoc, div_mul_cancel₀ _ hx.ne']

/-- If the Chebyshev error is bounded by C t^(3/4), the upper-support
scaled derivative error integral has absolute value at most
C x^(3/4)(12 exp 9 - 84). Compare against a continuous integrable majorant. -/
theorem triangular18_upper_psi_error_integral_le {x C : ℝ} (hx : 0 < x)
    (hpsi : ∀ t : ℝ, 0 ≤ t → |Chebyshev.psi t - t| ≤ C * t ^ (3 / 4 : ℝ)) :
    |∫ t in x..(Real.exp 36 * x),
          (((t / x) ^ (-3 / 2 : ℝ) * (Real.log (t / x) / 2 - 19)) / x) * (Chebyshev.psi t - t)| ≤
      C * (x ^ (3 / 4 : ℝ) * (12 * Real.exp 9 - 84)) := by
  let d := fun t : ℝ ↦ ((t / x) ^ (-3 / 2 : ℝ) * (Real.log (t / x) / 2 - 19)) / x
  have he : (1 : ℝ) ≤ Real.exp 36 := Real.one_le_exp_iff.mpr (by norm_num only)
  have hab : x ≤ Real.exp 36 * x := (one_mul x).symm.trans_le (mul_le_mul_of_nonneg_right he hx.le)
  have hC : 0 ≤ C := by
    have h := hpsi 1 (by norm_num only)
    norm_num only [Real.one_rpow, mul_one] at h
    exact (abs_nonneg _).trans h
  have hc :
    ContinuousOn (fun t : ℝ ↦ C * (|d t| * t ^ (3 / 4 : ℝ))) (Set.uIcc x (Real.exp 36 * x)) := by
    rw [Set.uIcc_of_le hab]
    intro t ht
    have ht0 := lt_of_lt_of_le hx ht.1
    have hp := div_pos ht0 hx
    have hr :=
      (Real.continuousAt_rpow_const (t / x) (-3 / 2) (Or.inl hp.ne')).comp (f := fun z : ℝ ↦ z / x)
        (x := t) (continuousAt_id.div_const x)
    have hl :=
      (Real.continuousAt_log hp.ne').comp (f := fun z : ℝ ↦ z / x) (x := t)
        (continuousAt_id.div_const x)
    have hd : ContinuousAt d t := (hr.mul ((hl.div_const 2).sub continuousAt_const)).div_const x
    exact
      (continuousAt_const.mul
          (hd.abs.mul (Real.continuousAt_rpow_const t (3 / 4) (Or.inl ht0.ne')))).continuousWithinAt
  have hb :=
    intervalIntegral.norm_integral_le_of_norm_le (μ := MeasureTheory.volume) hab (f := fun t : ℝ ↦
      d t * (Chebyshev.psi t - t))
      (Filter.Eventually.of_forall
        (fun t ht ↦ by
          rw [Real.norm_eq_abs, abs_mul]
          have ht0 : 0 ≤ t := hx.le.trans ht.1.le
          have h := mul_le_mul_of_nonneg_left (hpsi t ht0) (abs_nonneg (d t))
          simpa only [mul_assoc, mul_comm, mul_left_comm] using h))
      hc.intervalIntegrable
  rw [intervalIntegral.integral_const_mul, Real.norm_eq_abs] at hb
  exact hb.trans_eq (congrArg (fun z : ℝ ↦ C * z) (triangular18_upper_scaled_variation_integral hx))

/-- At positive scale, the upper Abel main integral equals x(40 - 4 exp 18).
A linear substitution transfers the proved primitive integral; used for the full principal sum. -/
theorem triangular18_upper_scaled_main_integral {x : ℝ} (hx : 0 < x) :
    (∫ t in x..(Real.exp 36 * x),
        (((t / x) ^ (-3 / 2 : ℝ) * (Real.log (t / x) / 2 - 19)) / x) * t) =
      x * (40 - 4 * Real.exp 18) := by
  let g := fun u : ℝ ↦ u ^ (-3 / 2 : ℝ) * (Real.log u / 2 - 19) * u
  have he (t : ℝ) :
    (((t / x) ^ (-3 / 2 : ℝ) * (Real.log (t / x) / 2 - 19)) / x) * t = g (t / x) := by
    dsimp only [g]
    ring
  rw [intervalIntegral.integral_congr (fun t _ ↦ he t), intervalIntegral.integral_comp_div g hx.ne',
    mul_div_cancel_right₀ _ hx.ne', div_self hx.ne', smul_eq_mul]
  exact congrArg (fun z : ℝ ↦ x * z) triangular18_upper_main_integral

end PseudoPrime.Analysis
