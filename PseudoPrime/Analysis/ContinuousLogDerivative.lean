/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-! # Derivative of a continuous logarithm -/

public section

namespace PseudoPrime.Analysis

/-- A continuous logarithm of a differentiable nonzero complex-valued path
has derivative `f' / f` within the same set. Near the point, the logarithm
of `f(t) / f(x)` equals the difference of the chosen continuous logarithm;
the principal logarithm is differentiable at the ratio value one. -/
theorem hasDerivWithinAt_continuous_log {S : Set ℝ} {f g : ℝ → ℂ} {x : ℝ} {f' : ℂ} (hx : x ∈ S)
    (hg : ContinuousWithinAt g S x) (hf : HasDerivWithinAt f f' S x)
    (he : ∀ t ∈ S, Complex.exp (g t) = f t) : HasDerivWithinAt g (f' / f x) S x := by
  have hne : f x ≠ 0 := by
    rw [← he x hx]; exact Complex.exp_ne_zero _
  have hc : ContinuousWithinAt (fun t : ℝ => (g t - g x).im) S x :=
    Complex.continuous_im.continuousAt.comp_continuousWithinAt (hg.sub continuousWithinAt_const)
  have h0 : (g x - g x).im = 0 := by rw [sub_self, Complex.zero_im]
  have hn : Set.Ioo (-Real.pi) Real.pi ∈ nhds ((g x - g x).im) := by
    rw [h0]
    exact Ioo_mem_nhds (neg_neg_of_pos Real.pi_pos) Real.pi_pos
  have hlocal :
    (fun t : ℝ => g t - g x) =ᶠ[nhdsWithin x S] (fun t : ℝ => Complex.log (f t / f x)) := by
    have hevent := hc.tendsto.eventually hn
    filter_upwards [hevent, self_mem_nhdsWithin] with t ht hts
    have heq : f t / f x = Complex.exp (g t - g x) := by rw [Complex.exp_sub, he t hts, he x hx]
    rw [heq, Complex.log_exp ht.1 ht.2.le]
  have hq : f x / f x = 1 := div_self hne
  have hdq : HasDerivWithinAt (fun t : ℝ => f t / f x) (f' / f x) S x := hf.div_const _
  have hl : HasDerivAt Complex.log 1 (f x / f x) := by
    rw [hq]
    simpa only [inv_one] using Complex.hasDerivAt_log Complex.one_mem_slitPlane
  have hdlog : HasDerivWithinAt (fun t : ℝ => Complex.log (f t / f x)) (f' / f x) S x := by
    simpa only [Function.comp_def, one_mul] using hl.comp_hasDerivWithinAt x hdq
  have hdsub := hdlog.congr_of_eventuallyEq_of_mem hlocal hx
  have hd := hdsub.add_const (g x)
  have heq : (fun t : ℝ => (g t - g x) + g x) = g := by
    funext t
    exact sub_add_cancel (g t) (g x)
  rw [heq] at hd
  exact hd

/-- A continuous real argument in a polar representation of a nonzero
differentiable complex path has derivative equal to the imaginary part of
its logarithmic derivative. Form a continuous logarithm using the real log
of the norm and take the imaginary part of its derivative. -/
theorem hasDerivWithinAt_continuous_arg {S : Set ℝ} {f : ℝ → ℂ} {φ : ℝ → ℝ} {x : ℝ} {f' : ℂ}
    (hx : x ∈ S) (hφ : ContinuousWithinAt φ S x) (hf : HasDerivWithinAt f f' S x)
    (hne : ∀ t ∈ S, f t ≠ 0)
    (hpolar : ∀ t ∈ S, f t = (‖f t‖ : ℂ) * Complex.exp ((φ t : ℂ) * Complex.I)) :
    HasDerivWithinAt φ (f' / f x).im S x := by
  let g : ℝ → ℂ := fun t => (Real.log ‖f t‖ : ℂ) + (φ t : ℂ) * Complex.I
  have hnorm : ‖f x‖ ≠ 0 := norm_ne_zero_iff.mpr (hne x hx)
  have hlog :=
    (Real.continuousAt_log hnorm).comp_continuousWithinAt (f := fun t : ℝ => ‖f t‖)
      hf.continuousWithinAt.norm
  have hlogC :=
    Complex.continuous_ofReal.continuousAt.comp_continuousWithinAt (f := fun t : ℝ =>
      Real.log ‖f t‖) hlog
  have hφC := Complex.continuous_ofReal.continuousAt.comp_continuousWithinAt (f := φ) hφ
  have hg : ContinuousWithinAt g S x := hlogC.add (hφC.mul continuousWithinAt_const)
  have he : ∀ t ∈ S, Complex.exp (g t) = f t := by
    intro t ht
    dsimp only [g]
    rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log (norm_pos_iff.mpr (hne t ht))]
    exact (hpolar t ht).symm
  have hd := hasDerivWithinAt_continuous_log hx hg hf he
  have hi := Complex.imCLM.hasFDerivAt.comp_hasDerivWithinAt x hd
  simpa only [Function.comp_def, Complex.imCLM_apply, g, Complex.add_im, Complex.ofReal_im,
    Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, zero_mul, add_zero,
    zero_add] using hi

end PseudoPrime.Analysis
