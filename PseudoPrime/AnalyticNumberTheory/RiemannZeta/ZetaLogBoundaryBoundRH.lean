/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaLogPhaseRH
public import PseudoPrime.Analysis.ComplexLogBoundaryBound

/-! # Local bounds for the zeta logarithm at the critical boundary -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Every Euler-normalized zeta logarithm on the upper strip exponentiates
to zeta. The identity theorem extends the Euler-product identity from the
part of the strip to the right of one. -/
theorem exp_strip_zeta_log {f : ℂ → ℂ}
    (hf :
      ∀ z : ℂ,
        1 / 2 < z.re →
          z.re < 5 / 2 →
          1 < z.im →
          HasDerivAt f (logDeriv riemannZeta z) z ∧
            (f z).re = Real.log ‖riemannZeta z‖ ∧ (1 < z.re → f z = backlundZetaLog z))
    {z : ℂ} (hz1 : 1 / 2 < z.re) (hz2 : z.re < 5 / 2) (hz3 : 1 < z.im) :
    Complex.exp (f z) = riemannZeta z := by
  let U : Set ℂ := ({z : ℂ | (1 / 2 : ℝ) < z.re} ∩ {z : ℂ | z.re < 5 / 2}) ∩ {z : ℂ | 1 < z.im}
  have ho : IsOpen U :=
    ((isOpen_lt continuous_const Complex.continuous_re).inter
          (isOpen_lt Complex.continuous_re continuous_const)).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hc : IsPreconnected U :=
    (((convex_halfSpace_re_gt (1 / 2)).inter (convex_halfSpace_re_lt (5 / 2))).inter
        (convex_halfSpace_im_gt 1)).isPreconnected
  have hd : DifferentiableOn ℂ f U := by
    intro w hw
    exact (hf w hw.1.1 hw.1.2 hw.2).1.differentiableAt.differentiableWithinAt
  have hfa : AnalyticOnNhd ℂ (fun w ↦ Complex.exp (f w)) U := (hd.analyticOnNhd ho).cexp
  have hza : AnalyticOnNhd ℂ riemannZeta U := by
    intro w hw
    apply analyticOn_riemannZeta
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro he
    have hi : 1 < w.im := hw.2
    rw [he, Complex.one_im] at hi
    linarith only [hi]
  let w : ℂ := (((2 : ℝ) : ℂ) + ((2 : ℝ) : ℂ) * Complex.I)
  have hw : w ∈ U := by
    simp only [U, Set.mem_inter_iff, Set.mem_ofPred_eq, w, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
    norm_num only [and_self]
  have hw1 : 1 < w.re := by
    simp only [w, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    norm_num only
  have hnear : (fun w ↦ Complex.exp (f w)) =ᶠ[nhds w] riemannZeta := by
    filter_upwards [ho.mem_nhds hw,
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hw1] with s hs hs1
    rw [(hf s hs.1.1 hs.1.2 hs.2).2.2 hs1, exp_backlundZetaLog hs1]
  exact hfa.eqOn_of_preconnected_of_eventuallyEq hza hc hw hnear ⟨⟨hz1, hz2⟩, hz3⟩

/-- At every point of the critical line above height one, an
Euler-normalized zeta logarithm has bounded imaginary part on a sufficiently
small right half-disk. This includes points where zeta vanishes, using the
finite order of its analytic zero. -/
theorem strip_log_boundary_local_bound {f : ℂ → ℂ} {c : ℂ} (hc : c.re = 1 / 2) (hci : 1 < c.im)
    (hf :
      ∀ z : ℂ,
        1 / 2 < z.re →
          z.re < 5 / 2 →
          1 < z.im →
          HasDerivAt f (logDeriv riemannZeta z) z ∧
            (f z).re = Real.log ‖riemannZeta z‖ ∧ (1 < z.re → f z = backlundZetaLog z)) :
    ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, ∀ z ∈ Metric.ball c r, 1 / 2 < z.re → |(f z).im| ≤ C := by
  have hc1 : c ≠ 1 := by
    intro heq
    have hi := congrArg Complex.im heq
    simp only [Complex.one_im] at hi
    linarith only [hci, hi]
  have hnt : ∀ n : ℕ, c ≠ -2 * (n + 1) := by
    intro n heq
    have hi := congrArg Complex.im heq
    have hr : (-2 * (n + 1) : ℂ) = (((-2 * ((n : ℝ) + 1) : ℝ)) : ℂ) := by
      push_cast
      ring
    rw [hr, Complex.ofReal_im] at hi
    linarith only [hci, hi]
  have horder : analyticOrderAt riemannZeta c ≠ ⊤ := by
    rw [← RiemannXi.analyticOrderAt_riemannXi_eq_riemannZeta (by linarith only [hc]) hc1 hnt]
    exact RiemannXi.riemannXi_analyticOrderAt_ne_top c
  let V : Set ℂ := {z : ℂ | z.re < 5 / 2} ∩ {z : ℂ | 1 < z.im}
  have ho : IsOpen V :=
    (isOpen_lt Complex.continuous_re continuous_const).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hcmem : c ∈ V :=
    ⟨by
      change c.re < 5 / 2; linarith only [hc], hci⟩
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp (ho.mem_nhds hcmem)
  have hfd : ∀ z ∈ Metric.ball c R, c.re < z.re → DifferentiableAt ℂ f z := by
    intro z hz hzr
    have hzV := hball hz
    exact (hf z (by linarith only [hc, hzr]) hzV.1 hzV.2).1.differentiableAt
  have hexp : ∀ z ∈ Metric.ball c R, c.re < z.re → Complex.exp (f z) = riemannZeta z := by
    intro z hz hzr
    have hzV := hball hz
    exact exp_strip_zeta_log hf (by linarith only [hc, hzr]) hzV.1 hzV.2
  obtain ⟨r, hr, C, hC⟩ :=
    Analysis.analytic_boundary_log_im_bound hR (analyticOn_riemannZeta c hc1) horder hfd hexp
  exact ⟨r, hr, C, fun z hz hzre ↦ hC z hz (by linarith only [hc, hzre])⟩

/-- For every finite height interval above one, an Euler-normalized zeta
logarithm has uniformly bounded imaginary part on a fixed-width strip to
the right of the critical line. Compactness combines the local bounds,
including those at zero ordinates. -/
theorem strip_log_boundary_uniform_bound {f : ℂ → ℂ} {u v : ℝ} (hu : 1 < u)
    (hf :
      ∀ z : ℂ,
        1 / 2 < z.re →
          z.re < 5 / 2 →
          1 < z.im →
          HasDerivAt f (logDeriv riemannZeta z) z ∧
            (f z).re = Real.log ‖riemannZeta z‖ ∧ (1 < z.re → f z = backlundZetaLog z)) :
    ∃ δ : ℝ,
      0 < δ ∧
        ∃ B : ℝ,
          ∀ a y : ℝ,
            1 / 2 < a →
              a < 1 / 2 + δ → y ∈ Set.Icc u v → |(f ((a : ℂ) + (y : ℂ) * Complex.I)).im| ≤ B := by
  let point : ℝ → ℂ := fun y ↦ (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)
  let K : Set ℂ := point '' Set.Icc u v
  have hpoint : Continuous point :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hK : IsCompact K := isCompact_Icc.image hpoint
  have hlocal :
    ∀ c ∈ K, ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, ∀ z ∈ Metric.ball c r, 1 / 2 < z.re → |(f z).im| ≤ C := by
    intro c hc
    obtain ⟨y, hy, rfl⟩ := hc
    have hre : (point y).re = 1 / 2 := by
      simp only [point, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
        Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    have him : 1 < (point y).im := by
      simp only [point, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
      exact hu.trans_le hy.1
    exact strip_log_boundary_local_bound hre him hf
  obtain ⟨δ, hδ, B, hB⟩ := Analysis.compact_boundary_im_bound hK hlocal
  refine ⟨δ, hδ, B, ?_⟩
  intro a y ha haδ hy
  have hyK : point y ∈ K := ⟨y, hy, rfl⟩
  have hdist : dist ((a : ℂ) + (y : ℂ) * Complex.I) (point y) = |a - 1 / 2| := by
    rw [dist_eq_norm]
    have he : (a : ℂ) + (y : ℂ) * Complex.I - point y = ((a - 1 / 2 : ℝ) : ℂ) := by
      dsimp only [point]
      push_cast
      ring
    rw [he, Complex.norm_real, Real.norm_eq_abs]
  have hnear : ((a : ℂ) + (y : ℂ) * Complex.I) ∈ Metric.thickening δ K := by
    apply Metric.mem_thickening_iff.mpr
    refine ⟨point y, hyK, ?_⟩
    rw [hdist, abs_of_pos (by linarith only [ha] : 0 < a - 1 / 2)]
    linarith only [haδ]
  apply hB _ hnear
  simp only [Complex.add_re, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.I_re,
    Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  exact ha

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
