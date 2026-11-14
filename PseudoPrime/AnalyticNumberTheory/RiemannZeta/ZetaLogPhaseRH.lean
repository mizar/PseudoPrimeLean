/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCountGoodPhaseRH
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaLogHalfPlaneRH
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaLogCoherenceRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.BacklundArgDerivative

/-! # Local zeta logarithm and Euler-normalized phase -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- At a positive good height, an Euler-normalized horizontal phase agrees
with the imaginary part of any zeta logarithmic primitive on an interval
ending at 3/2 and normalized there. Their derivatives agree at interior
points, and their difference has zero integral derivative. -/
theorem phase_eq_log_im_of_deriv {t a : ℝ} (ht : 0 < t) (ha : -(1 / 2 : ℝ) ≤ a) (hab : a < 3 / 2)
    (hgood : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 ≤ ρ.re → ρ.im ≠ t) (φ : ℝ → ℝ) (f : ℂ → ℂ)
    (hc : ContinuousOn φ (Set.Icc (-(1 / 2)) (3 / 2)))
    (hp :
      ∀ x : ℝ,
        x ∈ Set.Icc (-(1 / 2)) (3 / 2) →
          riemannZeta ((x : ℂ) + (t : ℂ) * Complex.I) =
            (‖riemannZeta ((x : ℂ) + (t : ℂ) * Complex.I)‖ : ℂ) *
              Complex.exp ((φ x : ℂ) * Complex.I))
    (hn : φ (3 / 2) = (f (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).im)
    (hf :
      ∀ x ∈ Set.Icc a (3 / 2),
        HasDerivAt f (logDeriv riemannZeta ((x : ℂ) + (t : ℂ) * Complex.I))
          ((x : ℂ) + (t : ℂ) * Complex.I)) :
    φ a = (f ((a : ℂ) + (t : ℂ) * Complex.I)).im := by
  let g : ℝ → ℝ := fun x ↦ φ x - (f ((x : ℂ) + (t : ℂ) * Complex.I)).im
  have hsub : Set.Icc a (3 / 2 : ℝ) ⊆ Set.Icc (-(1 / 2)) (3 / 2) := by
    intro x hx
    exact ⟨ha.trans hx.1, hx.2⟩
  have hcont : ContinuousOn g (Set.uIcc a (3 / 2)) := by
    rw [Set.uIcc_of_le hab.le]
    apply (hc.mono hsub).sub
    intro x hx
    have hlin : ContinuousAt (fun y : ℝ ↦ (y : ℂ) + (t : ℂ) * Complex.I) x :=
      (Complex.continuous_ofReal.add continuous_const).continuousAt
    have hcomp : ContinuousAt (fun y : ℝ ↦ f ((y : ℂ) + (t : ℂ) * Complex.I)) x :=
      ContinuousAt.comp (f := fun y : ℝ ↦ (y : ℂ) + (t : ℂ) * Complex.I) (hf x hx).continuousAt hlin
    exact (Complex.continuous_im.continuousAt.comp hcomp).continuousWithinAt
  have hd : ∀ x ∈ Set.Ioo (min a (3 / 2)) (max a (3 / 2)), HasDerivWithinAt g 0 (Set.Ioi x) x := by
    intro x hx
    rw [min_eq_left hab.le, max_eq_right hab.le] at hx
    have hxfull : x ∈ Set.Icc (-(1 / 2) : ℝ) (3 / 2) := ⟨ha.trans hx.1.le, hx.2.le⟩
    have hφ := zeta_horizontal_arg_deriv ht hgood hc hp hxfull
    have hφ' := hφ.hasDerivAt (Icc_mem_nhds (ha.trans_lt hx.1) hx.2)
    have hline :=
      (hf x ⟨hx.1.le, hx.2.le⟩).comp (x : ℂ)
        ((hasDerivAt_id (x : ℂ)).add_const ((t : ℂ) * Complex.I))
    have hreal := hline.comp_ofReal
    have him := Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hreal
    have hdiff := hφ'.sub him
    have he : HasDerivAt g 0 x := by
      convert hdiff using 1
      · funext y
        rfl
      · simp only [Complex.imCLM_apply, mul_one, sub_self]
    exact he.hasDerivWithinAt
  have h :=
    intervalIntegral.integral_eq_sub_of_hasDeriv_right hcont hd
      (intervalIntegrable_const :
        IntervalIntegrable (fun _ : ℝ ↦ (0 : ℝ)) MeasureTheory.volume a (3 / 2))
  rw [intervalIntegral.integral_zero] at h
  dsimp only [g] at h
  linarith only [h, hn]

/-- Under RH, at every good height at least 100, an Euler-normalized local
zeta logarithm has boundary imaginary part π times the count-defined
argument as the real part approaches 1/2 from the right. The phase is
continuous at the good-height endpoint. -/
theorem exists_log_boundary_count (hRH : RiemannHypothesis) {t : ℝ} (ht : 100 ≤ t)
    (hgood : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 ≤ ρ.re → ρ.im ≠ t) :
    let c : ℂ := (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)
    ∃ f : ℂ → ℂ,
      (∀ s ∈ Metric.ball c 1, HasDerivAt f (logDeriv riemannZeta s) s) ∧
        (∀ s ∈ Metric.ball c 1, (f s).re = Real.log ‖riemannZeta s‖) ∧
        (∀ s ∈ Metric.ball c 1, 1 < s.re → f s = backlundZetaLog s) ∧
        Filter.Tendsto (fun a : ℝ ↦ (f ((a : ℂ) + (t : ℂ) * Complex.I)).im)
          (nhdsWithin (1 / 2 : ℝ) (Set.Ioi (1 / 2))) (nhds (Real.pi * zetaArgCount t)) := by
  dsimp only
  have ht0 : 0 < t := by linarith only [ht]
  obtain ⟨f, hf, hre, heuler⟩ :=
    exists_zeta_log_near_backlund hRH (show 1 < t by linarith only [ht])
  obtain ⟨φ, hc, hp, hn, hcount⟩ := exists_euler_phase_of_count hRH ht hgood
  have hcenter :
    (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) ∈
      Metric.ball (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) 1 :=
    Metric.mem_ball_self (by norm_num only)
  have hfcenter :=
    heuler _ hcenter
      (by
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
        norm_num only)
  have hanchor : φ (3 / 2) = (f (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).im := by
    rw [hfcenter]
    exact hn
  have hphase : ∀ a : ℝ, 1 / 2 < a → a < 3 / 2 → φ a = (f ((a : ℂ) + (t : ℂ) * Complex.I)).im := by
    intro a ha hab
    apply phase_eq_log_im_of_deriv ht0 (by linarith only [ha]) hab hgood φ f hc hp hanchor
    intro x hx
    apply hf
    rw [Metric.mem_ball, dist_eq_norm]
    have he :
      ((x : ℂ) + (t : ℂ) * Complex.I) - (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) =
        ((x - 3 / 2 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_lt]
    constructor <;> linarith only [ha, hx.1, hx.2]
  have hnear :
    ∀ᶠ a : ℝ in nhdsWithin (1 / 2 : ℝ) (Set.Ioi (1 / 2)),
      (f ((a : ℂ) + (t : ℂ) * Complex.I)).im = φ a := by
    have hpos : ∀ᶠ a : ℝ in nhdsWithin (1 / 2 : ℝ) (Set.Ioi (1 / 2)), 1 / 2 < a :=
      self_mem_nhdsWithin
    have hlt : ∀ᶠ a : ℝ in nhdsWithin (1 / 2 : ℝ) (Set.Ioi (1 / 2)), a < 3 / 2 :=
      (eventually_lt_nhds (by norm_num only : (1 / 2 : ℝ) < 3 / 2)).filter_mono nhdsWithin_le_nhds
    filter_upwards [hpos, hlt] with a ha hab
    exact (hphase a ha hab).symm
  have hcont :=
    (hc (1 / 2) (by constructor <;> norm_num only)).continuousAt
      (Icc_mem_nhds (by norm_num only) (by norm_num only))
  have hlim := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (1 / 2 : ℝ)))
  refine ⟨f, hf, hre, heuler, ?_⟩
  rw [hcount]
  apply hlim.congr'
  filter_upwards [hnear] with a ha
  exact ha.symm

/-- Under RH, almost every height at least 100 admits an Euler-normalized
local zeta logarithm whose right-hand boundary imaginary part equals π
times the count-defined argument. Zero ordinates are a null set. -/
theorem ae_exists_log_boundary_count (hRH : RiemannHypothesis) :
    ∀ᵐ t : ℝ,
      100 ≤ t →
        ∃ f : ℂ → ℂ,
          (∀ s ∈ Metric.ball (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) 1,
              HasDerivAt f (logDeriv riemannZeta s) s) ∧
            (∀ s ∈ Metric.ball (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) 1,
              (f s).re = Real.log ‖riemannZeta s‖) ∧
            (∀ s ∈ Metric.ball (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) 1,
              1 < s.re → f s = backlundZetaLog s) ∧
            Filter.Tendsto (fun a : ℝ ↦ (f ((a : ℂ) + (t : ℂ) * Complex.I)).im)
              (nhdsWithin (1 / 2 : ℝ) (Set.Ioi (1 / 2))) (nhds (Real.pi * zetaArgCount t)) := by
  filter_upwards [ae_zeta_good_height] with t hgood ht
  exact exists_log_boundary_count hRH ht hgood

/-- At a good height at least 100, any Euler-normalized logarithm on the
upper strip has boundary imaginary part π times the count-defined
argument. Compare its horizontal derivative with the continuous normalized
phase and use the phase's endpoint continuity. -/
theorem strip_log_boundary_of_count (hRH : RiemannHypothesis) {t : ℝ} (ht : 100 ≤ t)
    (hgood : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 ≤ ρ.re → ρ.im ≠ t) (f : ℂ → ℂ)
    (hf :
      ∀ z : ℂ,
        1 / 2 < z.re →
          z.re < 5 / 2 →
          1 < z.im →
          HasDerivAt f (logDeriv riemannZeta z) z ∧
            (f z).re = Real.log ‖riemannZeta z‖ ∧ (1 < z.re → f z = backlundZetaLog z)) :
    Filter.Tendsto (fun a : ℝ ↦ (f ((a : ℂ) + (t : ℂ) * Complex.I)).im)
      (nhdsWithin (1 / 2 : ℝ) (Set.Ioi (1 / 2))) (nhds (Real.pi * zetaArgCount t)) := by
  have ht0 : 0 < t := by linarith only [ht]
  obtain ⟨φ, hc, hp, hn, hcount⟩ := exists_euler_phase_of_count hRH ht hgood
  have hfcenter :=
    hf (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)
      (by
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
        norm_num only)
      (by
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
        norm_num only)
      (by
        simp only [Complex.add_im, Complex.ofReal_im, Complex.ofReal_re, Complex.mul_im,
          Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
        linarith only [ht])
  have hanchor : φ (3 / 2) = (f (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).im := by
    rw [hfcenter.2.2
        (by
          simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
            Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
          norm_num only)]
    exact hn
  have hphase : ∀ a : ℝ, 1 / 2 < a → a < 3 / 2 → φ a = (f ((a : ℂ) + (t : ℂ) * Complex.I)).im := by
    intro a ha hab
    apply phase_eq_log_im_of_deriv ht0 (by linarith only [ha]) hab hgood φ f hc hp hanchor
    intro x hx
    apply (hf ((x : ℂ) + (t : ℂ) * Complex.I) ?_ ?_ ?_).1
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
      linarith only [ha, hx.1]
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
      linarith only [hx.2]
    · simp only [Complex.add_im, Complex.ofReal_im, Complex.ofReal_re, Complex.mul_im, Complex.I_re,
        Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
      linarith only [ht]
  have hnear :
    ∀ᶠ a : ℝ in nhdsWithin (1 / 2 : ℝ) (Set.Ioi (1 / 2)),
      φ a = (f ((a : ℂ) + (t : ℂ) * Complex.I)).im := by
    have hpos : ∀ᶠ a : ℝ in nhdsWithin (1 / 2 : ℝ) (Set.Ioi (1 / 2)), 1 / 2 < a :=
      self_mem_nhdsWithin
    have hlt : ∀ᶠ a : ℝ in nhdsWithin (1 / 2 : ℝ) (Set.Ioi (1 / 2)), a < 3 / 2 :=
      (eventually_lt_nhds (by norm_num only : (1 / 2 : ℝ) < 3 / 2)).filter_mono nhdsWithin_le_nhds
    filter_upwards [hpos, hlt] with a ha hab
    exact hphase a ha hab
  have hcont :=
    (hc (1 / 2) (by constructor <;> norm_num only)).continuousAt
      (Icc_mem_nhds (by norm_num only) (by norm_num only))
  have hlim := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (1 / 2 : ℝ)))
  rw [hcount]
  exact hlim.congr' hnear

/-- Under RH, there is a single Euler-normalized zeta logarithm on the upper
strip whose right boundary values recover the count-defined argument at
almost every height at least 100. This unifies the local boundary limits
needed for integration in height. -/
theorem exists_strip_log_with_count_boundary (hRH : RiemannHypothesis) :
    ∃ f : ℂ → ℂ,
      (∀ z : ℂ,
          1 / 2 < z.re →
            z.re < 5 / 2 →
            1 < z.im →
            HasDerivAt f (logDeriv riemannZeta z) z ∧
              (f z).re = Real.log ‖riemannZeta z‖ ∧ (1 < z.re → f z = backlundZetaLog z)) ∧
        ∀ᵐ t : ℝ,
          100 ≤ t →
            Filter.Tendsto (fun a : ℝ ↦ (f ((a : ℂ) + (t : ℂ) * Complex.I)).im)
              (nhdsWithin (1 / 2 : ℝ) (Set.Ioi (1 / 2))) (nhds (Real.pi * zetaArgCount t)) := by
  obtain ⟨f, hf⟩ := exists_zeta_log_on_upper_strip hRH
  refine ⟨f, hf, ?_⟩
  filter_upwards [ae_zeta_good_height] with t hgood ht
  exact strip_log_boundary_of_count hRH ht hgood f hf

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
