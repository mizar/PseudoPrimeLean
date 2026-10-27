/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.General.TriangularMellinContour
public import PseudoPrime.AnalyticNumberTheory.General.TriangularResolventInversion
public import PseudoPrime.AnalyticNumberTheory.RectangleGeometry.NonnegativeStripLimits

/-! # Central-line inversion for triangular resolvents -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.General

/-- For positive triangular parameter and argument and a pole with negative real part,
weighted resolvent integrals agree on nonnegative unit-strip lines. The pole distance
is bounded below and the kernel has quadratic decay. Apply the nonnegative strip theorem.
This permits central-line inversion despite a pole outside the strip. -/
theorem integral_triangular_resolvent_vertical_eq {α : ℂ} (hα : α.re < 0) {a c d u : ℝ} (ha : 0 < a)
    (hu : 0 < u) (hc : c ∈ Set.Icc (0 : ℝ) 1) (hd : d ∈ Set.Icc (0 : ℝ) 1) :
    (∫ t : ℝ,
        (Analysis.triangularMellinFunction a ((c : ℂ) + t * Complex.I) /
            (((c : ℂ) + t * Complex.I) - α)) *
          (u : ℂ) ^ (-((c : ℂ) + t * Complex.I))) =
      (∫ t : ℝ,
        (Analysis.triangularMellinFunction a ((d : ℂ) + t * Complex.I) /
            (((d : ℂ) + t * Complex.I) - α)) *
          (u : ℂ) ^ (-((d : ℂ) + t * Complex.I))) := by
  let f := fun s : ℂ ↦ (Analysis.triangularMellinFunction a s / (s - α)) * (u : ℂ) ^ (-s)
  have hδ : 0 < -α.re := neg_pos.mpr hα
  have hden (s : ℂ) (hs : 0 ≤ s.re) : -α.re ≤ ‖s - α‖ := by
    have h := Complex.re_le_norm (s - α)
    rw [Complex.sub_re] at h
    linarith only [hs, h]
  have hne (s : ℂ) (hs : 0 ≤ s.re) : s - α ≠ 0 := norm_pos_iff.mp (hδ.trans_le (hden s hs))
  have hf (s : ℂ) (hs : s.re ∈ Set.Icc (0 : ℝ) 1) : DifferentiableAt ℂ f s :=
    ((Analysis.differentiable_triangularMellinFunction a s).div (differentiableAt_id.sub_const α)
          (hne s hs.1)).mul
      ((differentiable_id.neg.const_cpow
          (Or.inl (Complex.ofReal_ne_zero.mpr hu.ne'))).differentiableAt)
  obtain ⟨C, hC, hK⟩ := Analysis.triangularMellinFunction_strip_bound ha
  have hpow (s : ℂ) (hs : s.re ∈ Set.Icc (0 : ℝ) 1) : ‖(u : ℂ) ^ (-s)‖ ≤ Real.exp |Real.log u| := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hu, Complex.neg_re, Real.rpow_def_of_pos hu]
    apply Real.exp_le_exp.mpr
    have hh : |Real.log u| * |s.re| ≤ |Real.log u| := by
      have hsr : |s.re| ≤ 1 := by
        rw [abs_of_nonneg hs.1]; exact hs.2
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hsr (abs_nonneg (Real.log u))
    have hl := le_abs_self (Real.log u * -s.re)
    rw [abs_mul, abs_neg] at hl
    exact hl.trans hh
  have hb (s : ℂ) (hs : s.re ∈ Set.Icc (0 : ℝ) 1) :
    ‖f s‖ ≤ (C * Real.exp |Real.log u| / (-α.re)) / (1 + ‖s‖ ^ 2) := by
    have hsr : |s.re| ≤ 1 := by
      rw [abs_of_nonneg hs.1]; exact hs.2
    have hn : ‖Analysis.triangularMellinFunction a s / (s - α)‖ ≤ C / (1 + ‖s‖ ^ 2) / (-α.re) := by
      rw [norm_div]
      exact
        (div_le_div_of_nonneg_left (norm_nonneg _) hδ (hden s hs.1)).trans
          (div_le_div_of_nonneg_right (hK s hsr) hδ.le)
    dsimp only [f]
    rw [norm_mul]
    have h :=
      mul_le_mul hn (hpow s hs) (norm_nonneg _)
        (div_nonneg (div_nonneg hC.le (by linarith only [sq_nonneg ‖s‖] : 0 ≤ 1 + ‖s‖ ^ 2)) hδ.le)
    exact h.trans_eq (by ring)
  have hi (r : ℝ) (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    MeasureTheory.Integrable (fun t : ℝ ↦ f ((r : ℂ) + t * Complex.I)) := by
    have hre (t : ℝ) : 0 ≤ ((r : ℂ) + t * Complex.I).re := by
      simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero] using hr.1
    have hcont : Continuous (fun t : ℝ ↦ 1 / (((r : ℂ) + t * Complex.I) - α)) :=
      continuous_const.div
        ((continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).sub
          continuous_const)
        (fun t ↦ hne _ (hre t))
    have hbase := integrable_inverseMellin_triangular (c := r) ha.ne' hu
    have h :=
      hbase.bdd_mul hcont.aestronglyMeasurable (c := 1 / (-α.re))
        (MeasureTheory.ae_of_all _
          (fun t ↦ by
            rw [norm_div, norm_one]
            exact one_div_le_one_div_of_le hδ (hden _ (hre t))))
    convert h using 1
    funext t
    dsimp only [f]
    simp only [div_eq_mul_inv, one_mul]
    ring_nf
  exact
    RectangleGeometry.integral_vertical_eq_of_nonnegative_strip_decay hf hc hd
      (div_nonneg (mul_nonneg hC.le (Real.exp_pos _).le) hδ.le) hb hi

/-- For positive parameter and argument and a pole with negative real part,
the central inverse transform equals the three translated regularized weights.
Shift to one quarter and apply positive-line resolvent inversion.
This connects the central digamma integral series to the explicit pole weights. -/
theorem mellinInv_triangular_resolvent_central_weight_combination {α : ℂ} (hα : α.re < 0) {a u : ℝ}
    (ha : 0 < a) (hu : 0 < u) :
    mellinInv 0 (fun s : ℂ ↦ Analysis.triangularMellinFunction a s / (s - α)) u =
      mellinResolventWeight α (u / Real.exp (2 * a)) +
          mellinResolventWeight α (u / Real.exp (-2 * a)) -
        2 * mellinResolventWeight α u := by
  rw [←
    mellinInv_triangular_resolvent_weight_combination hα ha.ne' (by norm_num only : (0 : ℝ) < 1 / 4)
      hu]
  unfold mellinInv
  congr 1
  have h :=
    integral_triangular_resolvent_vertical_eq hα ha hu (c := 0) (d := 1 / 4)
      (by constructor <;> norm_num only) (by constructor <;> norm_num only)
  simpa only [smul_eq_mul, mul_comm] using h

end PseudoPrime.AnalyticNumberTheory.General
