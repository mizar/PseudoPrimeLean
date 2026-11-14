/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannXi.HorizontalPoissonRH
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.EulerLog
import PseudoPrime.AnalyticNumberTheory.RiemannXi.LogFactor
import PseudoPrime.AnalyticNumberTheory.RiemannXi.ZeroFiniteness
import PseudoPrime.Analysis.ComplexLogPrimitive

/-! # Local zeta logarithms in the zero-free upper half-plane -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- To the right of one, the Euler logarithm has derivative ζ′/ζ.
Differentiate its exponential representation and cancel the nonzero
zeta value. This identifies the Euler normalization with any compatible
local logarithmic primitive. -/
theorem hasDerivAt_backlundZetaLog {s : ℂ} (hs : 1 < s.re) :
    HasDerivAt backlundZetaLog (logDeriv riemannZeta s) s := by
  have hd := (differentiableAt_backlundZetaLog hs).hasDerivAt
  have he : riemannZeta =ᶠ[nhds s] (fun z ↦ Complex.exp (backlundZetaLog z)) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
    exact (exp_backlundZetaLog hz).symm
  have hz := hd.cexp.congr_of_eventuallyEq he
  have hder : deriv riemannZeta s = Complex.exp (backlundZetaLog s) * deriv backlundZetaLog s :=
    hz.deriv
  have heq : logDeriv riemannZeta s = deriv backlundZetaLog s := by
    rw [logDeriv_apply, hder, ← exp_backlundZetaLog hs]
    exact mul_div_cancel_left₀ _ (Complex.exp_ne_zero _)
  rwa [heq]

/-- Under RH, zeta is nonzero to the right of the critical line at every
point other than its pole. A zero would also be an xi zero, contradicting
the RH location theorem. -/
theorem zeta_ne_zero_right_of_RH (hRH : RiemannHypothesis) {s : ℂ} (hs : 1 / 2 < s.re)
    (hs1 : s ≠ 1) : riemannZeta s ≠ 0 := by
  have hs0 : 0 < s.re := by linarith only [hs]
  have hx : RiemannXi.riemannXi s ≠ 0 := fun h ↦
    hs.ne' (RiemannXi.xi_zero_re_eq_half_of_riemannHypothesis hRH h)
  intro hz
  apply hx
  rw [RiemannXi.riemannXi_eq_exp_factor hs0 hs1, hz, mul_zero]

/-- Under RH, every disk contained in the upper half-plane to the right of
the critical line admits a holomorphic logarithmic primitive of zeta.
Its real part is the logarithm of the zeta norm. -/
theorem exists_zeta_log_on_ball (hRH : RiemannHypothesis) {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hball : ∀ s ∈ Metric.ball c r, 1 / 2 < s.re ∧ 0 < s.im) :
    ∃ f : ℂ → ℂ,
      (∀ s ∈ Metric.ball c r, HasDerivAt f (logDeriv riemannZeta s) s) ∧
        ∀ s ∈ Metric.ball c r, (f s).re = Real.log ‖riemannZeta s‖ := by
  apply Analysis.exists_hasDerivAt_logDeriv_re_eq_log_norm hr
  · intro s hs
    apply analyticOn_riemannZeta
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro he
    have hi := (hball s hs).2
    rw [he, Complex.one_im] at hi
    exact lt_irrefl _ hi
  · intro s hs
    apply zeta_ne_zero_right_of_RH hRH (hball s hs).1
    intro he
    have hi := (hball s hs).2
    rw [he, Complex.one_im] at hi
    exact lt_irrefl _ hi

/-- Under RH, a zero-free disk in the upper right half-plane centered at a
point with real part greater than one has a zeta logarithmic primitive
normalized to the Euler logarithm at its center. A purely imaginary
translation preserves the derivative and the logarithmic norm. -/
theorem exists_euler_zeta_log_on_ball (hRH : RiemannHypothesis) {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hc : 1 < c.re) (hball : ∀ s ∈ Metric.ball c r, 1 / 2 < s.re ∧ 0 < s.im) :
    ∃ f : ℂ → ℂ,
      f c = backlundZetaLog c ∧
        (∀ s ∈ Metric.ball c r, HasDerivAt f (logDeriv riemannZeta s) s) ∧
        ∀ s ∈ Metric.ball c r, (f s).re = Real.log ‖riemannZeta s‖ := by
  obtain ⟨f, hf, hre⟩ := exists_zeta_log_on_ball hRH hr hball
  let d : ℝ := (backlundZetaLog c).im - (f c).im
  let g : ℂ → ℂ := fun s ↦ f s + (d : ℂ) * Complex.I
  have hcenter : c ∈ Metric.ball c r := Metric.mem_ball_self hr
  have hreal : (backlundZetaLog c).re = Real.log ‖riemannZeta c‖ := by
    rw [← exp_backlundZetaLog hc, Complex.norm_exp, Real.log_exp]
  refine ⟨g, ?_, ?_, ?_⟩
  · apply Complex.ext
    · simp only [g, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
      exact (hre c hcenter).trans hreal.symm
    · simp only [g, d, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero]
      ring
  · intro s hs
    exact (hf s hs).add_const _
  · intro s hs
    simp only [g, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    exact hre s hs

/-- A zeta logarithmic primitive on a disk that is Euler-normalized at its
center agrees with the Euler logarithm throughout the disk's intersection
with the half-plane of real part greater than one. Their derivatives agree
on this convex open set. -/
theorem zeta_log_eq_euler_on_ball {c : ℂ} {r : ℝ} {f : ℂ → ℂ} (hr : 0 < r) (hc : 1 < c.re)
    (hfc : f c = backlundZetaLog c)
    (hf : ∀ s ∈ Metric.ball c r, HasDerivAt f (logDeriv riemannZeta s) s) {s : ℂ}
    (hs : s ∈ Metric.ball c r) (hs1 : 1 < s.re) : f s = backlundZetaLog s := by
  let U : Set ℂ := Metric.ball c r ∩ {z : ℂ | 1 < z.re}
  have hopen : IsOpen U :=
    Metric.isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_re)
  have hconn : IsPreconnected U :=
    ((convex_ball c r).inter (convex_halfSpace_re_gt 1)).isPreconnected
  have hd : ∀ z ∈ U, HasDerivAt (fun w ↦ f w - backlundZetaLog w) 0 z := by
    intro z hz
    have hh := (hf z hz.1).sub (hasDerivAt_backlundZetaLog hz.2)
    convert hh using 1
    simp only [sub_self]
  have hdiff : DifferentiableOn ℂ (fun w ↦ f w - backlundZetaLog w) U := by
    intro z hz
    exact (hd z hz).differentiableAt.differentiableWithinAt
  have hzero : U.EqOn (deriv (fun w ↦ f w - backlundZetaLog w)) 0 := by
    intro z hz
    exact (hd z hz).deriv
  have hconst :=
    hopen.is_const_of_deriv_eq_zero hconn hdiff hzero
      (show c ∈ U from ⟨Metric.mem_ball_self hr, hc⟩) (show s ∈ U from ⟨hs, hs1⟩)
  change f c - backlundZetaLog c = f s - backlundZetaLog s at hconst
  rw [hfc, sub_self] at hconst
  exact (sub_eq_zero.mp hconst.symm)

/-- Under RH, a zero-free upper-half-plane disk centered to the right of one
admits a zeta logarithmic primitive that agrees with the Euler logarithm
everywhere in their common domain. Its real part is the logarithmic norm. -/
theorem exists_zeta_log_extending_euler (hRH : RiemannHypothesis) {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hc : 1 < c.re) (hball : ∀ s ∈ Metric.ball c r, 1 / 2 < s.re ∧ 0 < s.im) :
    ∃ f : ℂ → ℂ,
      (∀ s ∈ Metric.ball c r, HasDerivAt f (logDeriv riemannZeta s) s) ∧
        (∀ s ∈ Metric.ball c r, (f s).re = Real.log ‖riemannZeta s‖) ∧
        ∀ s ∈ Metric.ball c r, 1 < s.re → f s = backlundZetaLog s := by
  obtain ⟨f, hfc, hf, hre⟩ := exists_euler_zeta_log_on_ball hRH hr hc hball
  exact ⟨f, hf, hre, fun s hs hs1 ↦ zeta_log_eq_euler_on_ball hr hc hfc hf hs hs1⟩

/-- A local primitive normalized to the Euler logarithm exponentiates to
zeta on the entire disk. The identity theorem extends the equality from
the part of the disk with real part greater than one. -/
theorem exp_zeta_log_on_ball {c : ℂ} {r : ℝ} {f : ℂ → ℂ} (hr : 0 < r) (hc : 1 < c.re)
    (hball : ∀ s ∈ Metric.ball c r, 1 / 2 < s.re ∧ 0 < s.im)
    (hf : ∀ s ∈ Metric.ball c r, HasDerivAt f (logDeriv riemannZeta s) s)
    (heuler : ∀ s ∈ Metric.ball c r, 1 < s.re → f s = backlundZetaLog s) :
    ∀ s ∈ Metric.ball c r, Complex.exp (f s) = riemannZeta s := by
  have hfd : DifferentiableOn ℂ f (Metric.ball c r) := by
    intro s hs
    exact (hf s hs).differentiableAt.differentiableWithinAt
  have hfa : AnalyticOnNhd ℂ (fun s ↦ Complex.exp (f s)) (Metric.ball c r) :=
    (hfd.analyticOnNhd Metric.isOpen_ball).cexp
  have hza : AnalyticOnNhd ℂ riemannZeta (Metric.ball c r) := by
    intro s hs
    apply analyticOn_riemannZeta
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro he
    have hi := (hball s hs).2
    rw [he, Complex.one_im] at hi
    exact lt_irrefl _ hi
  have hnear : (fun s ↦ Complex.exp (f s)) =ᶠ[nhds c] riemannZeta := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr),
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hc] with s hs hs1
    rw [heuler s hs hs1, exp_backlundZetaLog hs1]
  exact
    hfa.eqOn_of_preconnected_of_eventuallyEq hza (convex_ball c r).isPreconnected
      (Metric.mem_ball_self hr) hnear

/-- Under RH, every eligible upper-half-plane disk centered to the right of
one has a holomorphic zeta logarithm extending the Euler logarithm. Its
exponential equals zeta and its real part is the logarithmic norm. -/
theorem exists_zeta_holomorphic_log (hRH : RiemannHypothesis) {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hc : 1 < c.re) (hball : ∀ s ∈ Metric.ball c r, 1 / 2 < s.re ∧ 0 < s.im) :
    ∃ f : ℂ → ℂ,
      (∀ s ∈ Metric.ball c r, HasDerivAt f (logDeriv riemannZeta s) s) ∧
        (∀ s ∈ Metric.ball c r, (f s).re = Real.log ‖riemannZeta s‖) ∧
        (∀ s ∈ Metric.ball c r, Complex.exp (f s) = riemannZeta s) ∧
        ∀ s ∈ Metric.ball c r, 1 < s.re → f s = backlundZetaLog s := by
  obtain ⟨f, hf, hre, heuler⟩ := exists_zeta_log_extending_euler hRH hr hc hball
  exact ⟨f, hf, hre, exp_zeta_log_on_ball hr hc hball hf heuler, heuler⟩

/-- Under RH, at every height above one the unit disk centered at
`3/2 + it` admits a zeta logarithm extending the Euler logarithm.
The disk stays strictly right of the critical line and above the real axis. -/
theorem exists_zeta_log_near_backlund (hRH : RiemannHypothesis) {t : ℝ} (ht : 1 < t) :
    let c : ℂ := (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)
    ∃ f : ℂ → ℂ,
      (∀ s ∈ Metric.ball c 1, HasDerivAt f (logDeriv riemannZeta s) s) ∧
        (∀ s ∈ Metric.ball c 1, (f s).re = Real.log ‖riemannZeta s‖) ∧
        ∀ s ∈ Metric.ball c 1, 1 < s.re → f s = backlundZetaLog s := by
  dsimp only
  let c : ℂ := (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)
  have hc : 1 < c.re := by
    simp only [c, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    norm_num only
  apply exists_zeta_log_extending_euler hRH (by norm_num only) hc
  intro s hs
  have hd : ‖s - c‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hs
  have hr := (Complex.abs_re_le_norm (s - c)).trans_lt hd
  have hi := (Complex.abs_im_le_norm (s - c)).trans_lt hd
  have hcr : c.re = 3 / 2 := by
    simp only [c, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  have hci : c.im = t := by
    simp only [c, Complex.add_im, Complex.ofReal_re, Complex.mul_im, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
  rw [Complex.sub_re, hcr, abs_lt] at hr
  rw [Complex.sub_im, hci, abs_lt] at hi
  constructor <;> linarith only [hr.1, hi.1, ht]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
