/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaLogHalfPlaneRH

/-! # Coherence of local Euler-normalized zeta logarithms -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Two local zeta logarithmic primitives that agree with the Euler
logarithm to the right of one agree throughout the intersection of their
disks, provided that intersection contains a point to the right of one.
Analytic continuation applies on the convex intersection. -/
theorem zeta_logs_agree_on_overlap {c₁ c₂ : ℂ} {r₁ r₂ : ℝ} {f g : ℂ → ℂ}
    (hf : ∀ z ∈ Metric.ball c₁ r₁, HasDerivAt f (logDeriv riemannZeta z) z)
    (hg : ∀ z ∈ Metric.ball c₂ r₂, HasDerivAt g (logDeriv riemannZeta z) z)
    (hfe : ∀ z ∈ Metric.ball c₁ r₁, 1 < z.re → f z = backlundZetaLog z)
    (hge : ∀ z ∈ Metric.ball c₂ r₂, 1 < z.re → g z = backlundZetaLog z) {a : ℂ}
    (ha₁ : a ∈ Metric.ball c₁ r₁) (ha₂ : a ∈ Metric.ball c₂ r₂) (ha : 1 < a.re) :
    Set.EqOn f g (Metric.ball c₁ r₁ ∩ Metric.ball c₂ r₂) := by
  let U : Set ℂ := Metric.ball c₁ r₁ ∩ Metric.ball c₂ r₂
  have hopen : IsOpen U := Metric.isOpen_ball.inter Metric.isOpen_ball
  have hconn : IsPreconnected U := ((convex_ball c₁ r₁).inter (convex_ball c₂ r₂)).isPreconnected
  have hfd : DifferentiableOn ℂ f U := by
    intro z hz
    exact (hf z hz.1).differentiableAt.differentiableWithinAt
  have hgd : DifferentiableOn ℂ g U := by
    intro z hz
    exact (hg z hz.2).differentiableAt.differentiableWithinAt
  have hnear : f =ᶠ[nhds a] g := by
    filter_upwards [Metric.isOpen_ball.mem_nhds ha₁, Metric.isOpen_ball.mem_nhds ha₂,
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds ha] with z hz₁ hz₂ hz
    exact (hfe z hz₁ hz).trans (hge z hz₂ hz).symm
  exact
    (hfd.analyticOnNhd hopen).eqOn_of_preconnected_of_eventuallyEq (hgd.analyticOnNhd hopen) hconn
      ⟨ha₁, ha₂⟩ hnear

/-- Euler-normalized zeta logarithms on the unit disks centered at
`3/2 + iu` and `3/2 + iv` agree on their intersection when the heights
differ by less than two. The midpoint of the centers is an Euler anchor. -/
theorem zeta_logs_agree_at_near_heights {u v : ℝ} (huv : |u - v| < 2) {f g : ℂ → ℂ}
    (hf :
      ∀ z ∈ Metric.ball (((3 / 2 : ℝ) : ℂ) + (u : ℂ) * Complex.I) 1,
        HasDerivAt f (logDeriv riemannZeta z) z)
    (hg :
      ∀ z ∈ Metric.ball (((3 / 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I) 1,
        HasDerivAt g (logDeriv riemannZeta z) z)
    (hfe :
      ∀ z ∈ Metric.ball (((3 / 2 : ℝ) : ℂ) + (u : ℂ) * Complex.I) 1,
        1 < z.re → f z = backlundZetaLog z)
    (hge :
      ∀ z ∈ Metric.ball (((3 / 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I) 1,
        1 < z.re → g z = backlundZetaLog z) :
    Set.EqOn f g
      (Metric.ball (((3 / 2 : ℝ) : ℂ) + (u : ℂ) * Complex.I) 1 ∩
        Metric.ball (((3 / 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I) 1) := by
  let a : ℂ := (((3 / 2 : ℝ) : ℂ) + (((u + v) / 2 : ℝ) : ℂ) * Complex.I)
  have hm : |(u - v) / 2| < 1 := by
    rw [abs_div, abs_of_pos (show (0 : ℝ) < 2 by norm_num only)]
    linarith only [huv]
  have ha₁ : a ∈ Metric.ball (((3 / 2 : ℝ) : ℂ) + (u : ℂ) * Complex.I) 1 := by
    rw [Metric.mem_ball, dist_eq_norm]
    have he :
      a - (((3 / 2 : ℝ) : ℂ) + (u : ℂ) * Complex.I) = (((v - u) / 2 : ℝ) : ℂ) * Complex.I := by
      dsimp only [a]
      push_cast
      ring
    rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
    have he' : (v - u) / 2 = -((u - v) / 2) := by ring
    rw [he', abs_neg]
    exact hm
  have ha₂ : a ∈ Metric.ball (((3 / 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I) 1 := by
    rw [Metric.mem_ball, dist_eq_norm]
    have he :
      a - (((3 / 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I) = (((u - v) / 2 : ℝ) : ℂ) * Complex.I := by
      dsimp only [a]
      push_cast
      ring
    rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
    exact hm
  have ha : 1 < a.re := by
    simp only [a, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    norm_num only
  exact zeta_logs_agree_on_overlap hf hg hfe hge ha₁ ha₂ ha

/-- Under RH, choose an Euler-normalized local zeta logarithm at every
height above one. These choices agree on all overlaps of unit disks whose
center heights differ by less than two, providing coherent local data for
gluing along a vertical height interval. -/
theorem exists_coherent_zeta_logs (hRH : RiemannHypothesis) :
    ∃ F : ℝ → ℂ → ℂ,
      (∀ t : ℝ,
          1 < t →
            (∀ z ∈ Metric.ball (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) 1,
                HasDerivAt (F t) (logDeriv riemannZeta z) z) ∧
              (∀ z ∈ Metric.ball (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) 1,
                (F t z).re = Real.log ‖riemannZeta z‖) ∧
              (∀ z ∈ Metric.ball (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) 1,
                1 < z.re → F t z = backlundZetaLog z)) ∧
        ∀ u v : ℝ,
          1 < u →
            1 < v →
            |u - v| < 2 →
            Set.EqOn (F u) (F v)
              (Metric.ball (((3 / 2 : ℝ) : ℂ) + (u : ℂ) * Complex.I) 1 ∩
                Metric.ball (((3 / 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I) 1) := by
  classical
  have hex :
    ∀ t : ℝ,
      ∃ f : ℂ → ℂ,
        1 < t →
          (∀ z ∈ Metric.ball (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) 1,
              HasDerivAt f (logDeriv riemannZeta z) z) ∧
            (∀ z ∈ Metric.ball (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) 1,
              (f z).re = Real.log ‖riemannZeta z‖) ∧
            (∀ z ∈ Metric.ball (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) 1,
              1 < z.re → f z = backlundZetaLog z) := by
    intro t
    by_cases ht : 1 < t
    · obtain ⟨f, hf, hre, he⟩ := exists_zeta_log_near_backlund hRH ht
      exact ⟨f, fun _ ↦ ⟨hf, hre, he⟩⟩
    · exact ⟨0, fun h ↦ (ht h).elim⟩
  let F : ℝ → ℂ → ℂ := fun t ↦ Classical.choose (hex t)
  have hF :
    ∀ t : ℝ,
      1 < t →
        (∀ z ∈ Metric.ball (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) 1,
            HasDerivAt (F t) (logDeriv riemannZeta z) z) ∧
          (∀ z ∈ Metric.ball (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) 1,
            (F t z).re = Real.log ‖riemannZeta z‖) ∧
          (∀ z ∈ Metric.ball (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) 1,
            1 < z.re → F t z = backlundZetaLog z) :=
    fun t ↦ Classical.choose_spec (hex t)
  refine ⟨F, hF, ?_⟩
  intro u v hu hv huv
  exact zeta_logs_agree_at_near_heights huv (hF u hu).1 (hF v hv).1 (hF u hu).2.2 (hF v hv).2.2

/-- If coherent unit-disk logarithms are given at nearby heights, evaluating
the logarithm selected by a point's own imaginary part agrees with the
logarithm on any disk containing that point. This is the local consistency
needed for a single logarithm on their union. -/
theorem coherent_zeta_logs_self {F : ℝ → ℂ → ℂ} {t : ℝ} {z : ℂ} (ht : 1 < t) (hz : 1 < z.im)
    (hmem : z ∈ Metric.ball (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) 1)
    (hF :
      ∀ u v : ℝ,
        1 < u →
          1 < v →
          |u - v| < 2 →
          Set.EqOn (F u) (F v)
            (Metric.ball (((3 / 2 : ℝ) : ℂ) + (u : ℂ) * Complex.I) 1 ∩
              Metric.ball (((3 / 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I) 1)) :
    F z.im z = F t z := by
  let c : ℂ := (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)
  have hd : ‖z - c‖ < 1 := by simpa only [c, Metric.mem_ball, dist_eq_norm] using hmem
  have hr := (Complex.abs_re_le_norm (z - c)).trans_lt hd
  have hi := (Complex.abs_im_le_norm (z - c)).trans_lt hd
  have hcr : c.re = 3 / 2 := by
    simp only [c, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  have hci : c.im = t := by
    simp only [c, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
  rw [Complex.sub_re, hcr] at hr
  rw [Complex.sub_im, hci] at hi
  have hself : z ∈ Metric.ball (((3 / 2 : ℝ) : ℂ) + (z.im : ℂ) * Complex.I) 1 := by
    rw [Metric.mem_ball, dist_eq_norm]
    have he : z - (((3 / 2 : ℝ) : ℂ) + (z.im : ℂ) * Complex.I) = ((z.re - 3 / 2 : ℝ) : ℂ) := by
      apply Complex.ext
      · simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
          Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
      · simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero,
          sub_self]
    rw [he, Complex.norm_real, Real.norm_eq_abs]
    exact hr
  exact hF z.im t hz ht (lt_trans hi (by norm_num only)) ⟨hself, hmem⟩

/-- Under RH, the local Euler-normalized logarithms glue to one holomorphic
zeta logarithm on the strip `1/2 < re z < 5/2`, `1 < im z`. The local
choice at the point's own height is locally equal to every overlapping
choice, so its derivative is the zeta logarithmic derivative. -/
theorem exists_zeta_log_on_upper_strip (hRH : RiemannHypothesis) :
    ∃ f : ℂ → ℂ,
      ∀ z : ℂ,
        1 / 2 < z.re →
          z.re < 5 / 2 →
          1 < z.im →
          HasDerivAt f (logDeriv riemannZeta z) z ∧
            (f z).re = Real.log ‖riemannZeta z‖ ∧ (1 < z.re → f z = backlundZetaLog z) := by
  obtain ⟨F, hF, hcoh⟩ := exists_coherent_zeta_logs hRH
  let f : ℂ → ℂ := fun z ↦ F z.im z
  refine ⟨f, ?_⟩
  intro z hzlo hzhi hzim
  let c : ℂ := (((3 / 2 : ℝ) : ℂ) + (z.im : ℂ) * Complex.I)
  have hself : z ∈ Metric.ball c 1 := by
    rw [Metric.mem_ball, dist_eq_norm]
    have he : z - c = ((z.re - 3 / 2 : ℝ) : ℂ) := by
      apply Complex.ext
      · simp only [c, Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
          Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
      · simp only [c, Complex.sub_im, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero,
          sub_self]
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_lt]
    constructor <;> linarith only [hzlo, hzhi]
  have hnear : f =ᶠ[nhds z] F z.im := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hself,
      (isOpen_lt continuous_const Complex.continuous_im).mem_nhds hzim] with w hw hi
    exact coherent_zeta_logs_self hzim hi hw hcoh
  have hder := ((hF z.im hzim).1 z hself).congr_of_eventuallyEq hnear
  refine ⟨hder, ?_, ?_⟩
  · exact (hF z.im hzim).2.1 z hself
  · intro hz
    exact (hF z.im hzim).2.2 z hself hz

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
