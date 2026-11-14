/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaLogBoundaryBoundRH
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaLogFullRectangleRH
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import PseudoPrime.AnalyticNumberTheory.RiemannXi.HorizontalLogZetaRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCountArgumentIntegralRH

/-! # Passing the zeta-log boundary limit through integration -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- On a finite ordered height interval above 100, the integral of the
Euler-normalized logarithm's imaginary part converges to the integral of
π times the count argument. The uniform bound at all boundary points
dominates the almost-everywhere boundary convergence. -/
theorem strip_log_vertical_tendsto_count {f : ℂ → ℂ} {u v : ℝ} (hu : 100 ≤ u) (huv : u ≤ v)
    (hf :
      ∀ z : ℂ,
        1 / 2 < z.re →
          z.re < 5 / 2 →
          1 < z.im →
          HasDerivAt f (logDeriv riemannZeta z) z ∧
            (f z).re = Real.log ‖riemannZeta z‖ ∧ (1 < z.re → f z = backlundZetaLog z))
    (hboundary :
      ∀ᵐ t : ℝ,
        100 ≤ t →
          Filter.Tendsto (fun a : ℝ ↦ (f ((a : ℂ) + (t : ℂ) * Complex.I)).im)
            (nhdsWithin (1 / 2 : ℝ) (Set.Ioi (1 / 2))) (nhds (Real.pi * zetaArgCount t))) :
    Filter.Tendsto (fun a : ℝ ↦ ∫ y in u..v, (f ((a : ℂ) + (y : ℂ) * Complex.I)).im)
      (nhdsWithin (1 / 2 : ℝ) (Set.Ioi (1 / 2)))
      (nhds (∫ y in u..v, Real.pi * zetaArgCount y)) := by
  obtain ⟨δ, hδ, B, hB⟩ := strip_log_boundary_uniform_bound (by linarith only [hu] : 1 < u) hf
  have hlo : ∀ᶠ a : ℝ in nhdsWithin (1 / 2 : ℝ) (Set.Ioi (1 / 2)), 1 / 2 < a := self_mem_nhdsWithin
  have hhi : ∀ᶠ a : ℝ in nhdsWithin (1 / 2 : ℝ) (Set.Ioi (1 / 2)), a < 1 / 2 + δ :=
    (eventually_lt_nhds (by linarith only [hδ] : (1 / 2 : ℝ) < 1 / 2 + δ)).filter_mono
      nhdsWithin_le_nhds
  have hhi2 : ∀ᶠ a : ℝ in nhdsWithin (1 / 2 : ℝ) (Set.Ioi (1 / 2)), a < 5 / 2 :=
    (eventually_lt_nhds (by norm_num only : (1 / 2 : ℝ) < 5 / 2)).filter_mono nhdsWithin_le_nhds
  have hmeas :
    ∀ᶠ a : ℝ in nhdsWithin (1 / 2 : ℝ) (Set.Ioi (1 / 2)),
      MeasureTheory.AEStronglyMeasurable (fun y : ℝ ↦ (f ((a : ℂ) + (y : ℂ) * Complex.I)).im)
        (MeasureTheory.volume.restrict (Set.Ioc u v)) := by
    filter_upwards [hlo, hhi2] with a ha ha2
    have hd :
      ∀ z : ℂ, 1 / 2 < z.re → z.re < 5 / 2 → 1 < z.im → HasDerivAt f (logDeriv riemannZeta z) z :=
      fun z h1 h2 h3 ↦ (hf z h1 h2 h3).1
    have hi := zeta_log_vertical_integrable ha ha2 (by linarith only [hu] : 1 < u) huv hd
    have hin := (intervalIntegrable_iff_integrableOn_Ioc_of_le huv).mp hi
    exact (Complex.imCLM.integrable_comp hin).aestronglyMeasurable
  have hbound :
    ∀ᶠ a : ℝ in nhdsWithin (1 / 2 : ℝ) (Set.Ioi (1 / 2)),
      ∀ᵐ y : ℝ ∂(MeasureTheory.volume.restrict (Set.Ioc u v)),
        ‖(f ((a : ℂ) + (y : ℂ) * Complex.I)).im‖ ≤ B := by
    filter_upwards [hlo, hhi] with a ha haδ
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with y hy
    rw [Real.norm_eq_abs]
    exact hB a y ha haδ ⟨hy.1.le, hy.2⟩
  have hpoint :
    ∀ᵐ y : ℝ ∂(MeasureTheory.volume.restrict (Set.Ioc u v)),
      Filter.Tendsto (fun a : ℝ ↦ (f ((a : ℂ) + (y : ℂ) * Complex.I)).im)
        (nhdsWithin (1 / 2 : ℝ) (Set.Ioi (1 / 2))) (nhds (Real.pi * zetaArgCount y)) := by
    filter_upwards [MeasureTheory.ae_restrict_of_ae hboundary,
      MeasureTheory.ae_restrict_mem measurableSet_Ioc] with y hy hyuv
    exact hy (le_trans hu hyuv.1.le)
  have hconst :
    MeasureTheory.Integrable (fun _ : ℝ ↦ B) (MeasureTheory.volume.restrict (Set.Ioc u v)) :=
    MeasureTheory.integrableOn_const measure_Ioc_lt_top.ne enorm_ne_top
  have hlim :=
    MeasureTheory.tendsto_integral_filter_of_dominated_convergence (fun _ : ℝ ↦ B) hmeas hbound
      hconst hpoint
  simpa only [intervalIntegral.integral_of_le huv] using hlim

/-- Under RH, the integral of the count-defined argument equals the
difference of the horizontal ζ-logarithmic integrals, split at real part
two. The critical boundary is justified by dominated convergence and the
far right edge by Euler-log decay. -/
theorem count_arg_horizontal_split (hRH : RiemannHypothesis) {u v : ℝ} (hu : 100 ≤ u)
    (huv : u ≤ v) :
    Real.pi * (∫ t in u..v, zetaArgCount t) =
      ((∫ x in (1 / 2 : ℝ)..2, Real.log ‖riemannZeta ((x : ℂ) + (v : ℂ) * Complex.I)‖) -
          (∫ x in (1 / 2 : ℝ)..2, Real.log ‖riemannZeta ((x : ℂ) + (u : ℂ) * Complex.I)‖)) +
        ((∫ x in Set.Ioi (2 : ℝ), Real.log ‖riemannZeta ((x : ℂ) + (v : ℂ) * Complex.I)‖) -
          (∫ x in Set.Ioi (2 : ℝ), Real.log ‖riemannZeta ((x : ℂ) + (u : ℂ) * Complex.I)‖)) := by
  obtain ⟨f, hf, hboundary⟩ := exists_strip_log_with_count_boundary hRH
  have hcount := strip_log_vertical_tendsto_count hu huv hf hboundary
  rw [intervalIntegral.integral_const_mul] at hcount
  have hu0 : u ≠ 0 := (show (0 : ℝ) < u by linarith only [hu]).ne'
  have hv0 : v ≠ 0 := (show (0 : ℝ) < v by linarith only [hu, huv]).ne'
  have hlim :=
    ((tendsto_horizontal_logZeta_left hRH hv0).sub
          (tendsto_horizontal_logZeta_left hRH hu0)).add_const
      ((∫ x in Set.Ioi (2 : ℝ), Real.log ‖riemannZeta ((x : ℂ) + (v : ℂ) * Complex.I)‖) -
        (∫ x in Set.Ioi (2 : ℝ), Real.log ‖riemannZeta ((x : ℂ) + (u : ℂ) * Complex.I)‖))
  apply tendsto_nhds_unique hcount
  apply hlim.congr'
  have hlo : ∀ᶠ a : ℝ in nhdsWithin (1 / 2 : ℝ) (Set.Ioi (1 / 2)), 1 / 2 < a := self_mem_nhdsWithin
  have hhi : ∀ᶠ a : ℝ in nhdsWithin (1 / 2 : ℝ) (Set.Ioi (1 / 2)), a < 2 :=
    (eventually_lt_nhds (by norm_num only : (1 / 2 : ℝ) < 2)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hlo, hhi] with a ha ha2
  have hrect := zeta_log_rectangle_at_two ha ha2.le (by linarith only [hu] : 1 < u) huv hf
  have htail := zeta_log_tail_rectangle huv
  linarith only [hrect, htail]

/-- Translating the horizontal tail by one half preserves its integral.
The two improper integrals are limits of the same finite interval integral. -/
theorem horizontal_log_tail_shift (t : ℝ) :
    (∫ x in Set.Ioi (3 / 2 : ℝ),
        Real.log ‖riemannZeta (((1 / 2 + x : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖) =
      ∫ x in Set.Ioi (2 : ℝ), Real.log ‖riemannZeta ((x : ℂ) + (t : ℂ) * Complex.I)‖ := by
  let F : ℝ → ℝ := fun x ↦ Real.log ‖riemannZeta ((x : ℂ) + (t : ℂ) * Complex.I)‖
  have hd : MeasureTheory.IntegrableOn F (Set.Ioi (2 : ℝ)) := by
    have hi := Complex.reCLM.integrable_comp (integrable_eulerLog_horizontal t)
    apply hi.congr
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
    change (2 : ℝ) < x at hx
    have hs : 1 < (((x : ℂ) + (t : ℂ) * Complex.I)).re := by
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
      linarith only [hx]
    change (backlundZetaLog ((x : ℂ) + (t : ℂ) * Complex.I)).re = F x
    dsimp only [F]
    rw [← exp_backlundZetaLog hs, Complex.norm_exp, Real.log_exp]
  have hs : MeasureTheory.IntegrableOn (fun x : ℝ ↦ F (1 / 2 + x)) (Set.Ioi (3 / 2 : ℝ)) :=
    RiemannXi.integrable_horizontal_tail_of_real t integrable_log_zeta_real_tail
  have hlim1 :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi (3 / 2 : ℝ) hs
      (Filter.tendsto_id : Filter.Tendsto (fun x : ℝ ↦ x) Filter.atTop Filter.atTop)
  have hat : Filter.Tendsto (fun x : ℝ ↦ 1 / 2 + x) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono
      (fun x ↦ by
        change x ≤ 1 / 2 + x; linarith only)
      Filter.tendsto_id
  have hlim2 := MeasureTheory.intervalIntegral_tendsto_integral_Ioi (2 : ℝ) hd hat
  apply tendsto_nhds_unique hlim1
  apply hlim2.congr
  intro b
  have h := intervalIntegral.integral_comp_add_left F (1 / 2 : ℝ) (a := (3 / 2 : ℝ)) (b := b)
  norm_num only at h
  exact h.symm

/-- Under RH, the full horizontal logarithmic integral is the sum of its
finite part from one half to two and its right tail. Both integrals retain
the endpoint convention used by the rectangle identity. -/
theorem horizontal_log_split (hRH : RiemannHypothesis) {t : ℝ} (ht : t ≠ 0) :
    (∫ x in Set.Ioi (0 : ℝ), Real.log ‖riemannZeta (((1 / 2 + x : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖) =
      (∫ x in (1 / 2 : ℝ)..2, Real.log ‖riemannZeta ((x : ℂ) + (t : ℂ) * Complex.I)‖) +
        ∫ x in Set.Ioi (2 : ℝ), Real.log ‖riemannZeta ((x : ℂ) + (t : ℂ) * Complex.I)‖ := by
  let F : ℝ → ℝ := fun x ↦ Real.log ‖riemannZeta ((x : ℂ) + (t : ℂ) * Complex.I)‖
  have hf :=
    RiemannXi.intervalIntegrable_horizontal_logZeta hRH ht (show (0 : ℝ) ≤ 3 / 2 by norm_num only)
  have hi := RiemannXi.integrable_horizontal_tail_of_real t integrable_log_zeta_real_tail
  have hsplit := intervalIntegral.integral_interval_add_Ioi' hf hi
  have hfinite :=
    intervalIntegral.integral_comp_add_left F (1 / 2 : ℝ) (a := (0 : ℝ)) (b := (3 / 2 : ℝ))
  norm_num only at hfinite
  rw [hfinite, horizontal_log_tail_shift] at hsplit
  exact hsplit.symm

/-- Under RH, the count-defined argument satisfies the full horizontal
ζ-logarithm identity on every ordered height interval above 100. This
removes the analytic identity hypothesis from the integrated zero-count
error estimate. -/
theorem count_arg_horizontal (hRH : RiemannHypothesis) {u v : ℝ} (hu : 100 ≤ u) (huv : u ≤ v) :
    Real.pi * (∫ t in u..v, zetaArgCount t) =
      (∫ x in Set.Ioi (0 : ℝ),
          Real.log ‖riemannZeta (((1 / 2 + x : ℝ) : ℂ) + (v : ℂ) * Complex.I)‖) -
        (∫ x in Set.Ioi (0 : ℝ),
          Real.log ‖riemannZeta (((1 / 2 + x : ℝ) : ℂ) + (u : ℂ) * Complex.I)‖) := by
  have hu0 : u ≠ 0 := (show (0 : ℝ) < u by linarith only [hu]).ne'
  have hv0 : v ≠ 0 := (show (0 : ℝ) < v by linarith only [hu, huv]).ne'
  have h := count_arg_horizontal_split hRH hu huv
  rw [horizontal_log_split hRH hv0, horizontal_log_split hRH hu0]
  linarith only [h]

/-- Under RH, the count-defined zeta argument has a logarithmic integral
bound on ordered intervals starting at or above 100. The horizontal-log
identity and its two-sided bound supply the numerical constants. -/
theorem countArg_integral_bound (hRH : RiemannHypothesis) {u v : ℝ} (hu : 100 ≤ u) (huv : u ≤ v) :
    |∫ t in u..v, zetaArgCount t| ≤ 8 + (7 / 10 : ℝ) * Real.log v := by
  have hh := RiemannXi.abs_horizontal_logZeta_diff_le hRH hu huv
  rw [← count_arg_horizontal hRH hu huv, abs_mul, abs_of_pos Real.pi_pos] at hh
  have hl : 0 ≤ Real.log v := Real.log_nonneg (by linarith only [hu, huv])
  have hp := Real.pi_gt_three
  have hm := mul_nonneg (sub_nonneg.mpr hp.le) (abs_nonneg (∫ t in u..v, zetaArgCount t))
  nlinarith only [hh, hl, hm]

/-- Under RH, the moving primitive of twice the count-defined argument has
the scale-separated bound used with the combined reciprocal-zero kernel.
The dependence on `v / u` is kept separate from the lower-endpoint budget. -/
theorem countArg_moving_integral_bound (hRH : RiemannHypothesis) {u v : ℝ} (hu : 100 ≤ u)
    (huv : u ≤ v) :
    |∫ t in u..v, 2 * zetaArgCount t| ≤
      16 + (7 / 5 : ℝ) * Real.log u + (7 / 5 : ℝ) * Real.log (v / u) := by
  have hu0 : 0 < u := by linarith only [hu]
  have hv0 : 0 < v := hu0.trans_le huv
  have h := countArg_integral_bound hRH hu huv
  have hlog : Real.log (v / u) = Real.log v - Real.log u := Real.log_div hv0.ne' hu0.ne'
  rw [intervalIntegral.integral_const_mul, abs_mul, abs_of_nonneg (by norm_num only : (0 : ℝ) ≤ 2),
    hlog]
  linarith only [h]

/-- Under RH, the integrated two-sided zero-count error has the explicit
logarithmic bound on every ordered interval with lower endpoint at least
100. The horizontal identity is now proved from the normalized logarithm. -/
theorem countError_integral_bound (hRH : RiemannHypothesis) {u v : ℝ} (hu : 100 ≤ u) (huv : u ≤ v) :
    |∫ t in u..v, zeroCountError t| ≤
      16 + (7 / 5 : ℝ) * Real.log v + (2 / 5 : ℝ) * Real.log (v / u) := by
  exact countError_integral_of_horizontal hRH hu huv (count_arg_horizontal hRH hu huv)

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
