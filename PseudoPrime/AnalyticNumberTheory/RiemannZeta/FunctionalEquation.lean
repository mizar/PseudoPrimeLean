/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LogDerivConjugation
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GammaFactorLogDeriv

/-! # Functional equation for the zeta factor -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The zeta functional-equation factor `Γℝ(1 - s) / Γℝ(s)`. It is used
on horizontal segments away from the real axis, where both Gamma factors
are regular and nonzero. -/
noncomputable def backlundChi (z : ℂ) : ℂ :=
  Complex.Gammaℝ (1 - z) / Complex.Gammaℝ z

/-- Away from the real axis, the logarithmic derivative of the functional
equation factor is the negative sum of the two reflected Gamma-factor
logarithmic derivatives. Apply the quotient and chain rules at regular points. -/
theorem backlundChi_logDeriv {s : ℂ} (hs : s.im ≠ 0) :
    logDeriv backlundChi s = -logDeriv Complex.Gammaℝ (1 - s) - logDeriv Complex.Gammaℝ s := by
  have ht : (1 - s).im ≠ 0 := by
    simpa only [Complex.sub_im, Complex.one_im, zero_sub, neg_ne_zero] using hs
  have hp := AnalyticNumberTheory.DirichletLFunction.half_ne_neg_nat_of_im_ne_zero hs
  have hq := AnalyticNumberTheory.DirichletLFunction.half_ne_neg_nat_of_im_ne_zero ht
  have hd := AnalyticNumberTheory.DirichletLFunction.differentiableAt_Gammaℝ_of_nonpole hp
  have he := AnalyticNumberTheory.DirichletLFunction.differentiableAt_Gammaℝ_of_nonpole hq
  have hn := AnalyticNumberTheory.DirichletLFunction.Gammaℝ_ne_zero_of_half_ne_neg_nat hp
  have hm := AnalyticNumberTheory.DirichletLFunction.Gammaℝ_ne_zero_of_half_ne_neg_nat hq
  have hg : DifferentiableAt ℂ (fun z : ℂ => 1 - z) s := differentiableAt_id.const_sub 1
  have hf : DifferentiableAt ℂ (fun z : ℂ => Complex.Gammaℝ (1 - z)) s := he.comp s hg
  have hc :
    logDeriv (fun z : ℂ => Complex.Gammaℝ (1 - z)) s = -logDeriv Complex.Gammaℝ (1 - s) := by
    have hc := logDeriv_comp (f := Complex.Gammaℝ) (g := fun z : ℂ => 1 - z) he hg
    have hder : deriv (fun z : ℂ => 1 - z) s = -1 := by
      change deriv (fun z : ℂ => 1 - id z) s = -1
      exact ((hasDerivAt_id s).const_sub 1).deriv
    simp only [Function.comp_def, hder, mul_neg, mul_one] at hc
    exact hc
  change logDeriv ((fun z : ℂ => Complex.Gammaℝ (1 - z)) / Complex.Gammaℝ) s = _
  rw [logDeriv_div s hm hn hf hd, hc]

/-- Away from the real axis, zeta satisfies `ζ(s) = χ(s) ζ(1-s)` for the
Backlund factor `χ`. Divide the symmetric completed zeta function by the
regular nonzero Gamma factors. -/
theorem zeta_backlund_functional_eq {s : ℂ} (hs : s.im ≠ 0) :
    riemannZeta s = backlundChi s * riemannZeta (1 - s) := by
  have hs0 : s ≠ 0 := by
    intro h
    apply hs
    rw [h, Complex.zero_im]
  have ht : (1 - s).im ≠ 0 := by
    simpa only [Complex.sub_im, Complex.one_im, zero_sub, neg_ne_zero] using hs
  have ht0 : 1 - s ≠ 0 := by
    intro h
    apply ht
    rw [h, Complex.zero_im]
  have hq := AnalyticNumberTheory.DirichletLFunction.half_ne_neg_nat_of_im_ne_zero ht
  have hg := AnalyticNumberTheory.DirichletLFunction.Gammaℝ_ne_zero_of_half_ne_neg_nat hq
  rw [riemannZeta_def_of_ne_zero hs0, riemannZeta_def_of_ne_zero ht0, completedRiemannZeta_one_sub]
  dsimp only [backlundChi]
  rw [mul_comm, div_mul_div_cancel₀ hg]

/-- At a nonzero zeta value away from the real axis, the sum of the zeta
logarithmic derivatives at `s` and `1 - s` equals the logarithmic derivative
of the Backlund factor. Differentiate the functional equation locally and
use the product and chain rules at regular nonzero points. -/
theorem zeta_backlund_logDeriv {s : ℂ} (hs : s.im ≠ 0) (hz : riemannZeta s ≠ 0) :
    logDeriv riemannZeta s + logDeriv riemannZeta (1 - s) = logDeriv backlundChi s := by
  have ht : (1 - s).im ≠ 0 := by
    simpa only [Complex.sub_im, Complex.one_im, zero_sub, neg_ne_zero] using hs
  have ht1 : 1 - s ≠ 1 := by
    intro he
    apply ht
    rw [he, Complex.one_im]
  have hp := AnalyticNumberTheory.DirichletLFunction.half_ne_neg_nat_of_im_ne_zero hs
  have hq := AnalyticNumberTheory.DirichletLFunction.half_ne_neg_nat_of_im_ne_zero ht
  have hd := AnalyticNumberTheory.DirichletLFunction.differentiableAt_Gammaℝ_of_nonpole hp
  have he := AnalyticNumberTheory.DirichletLFunction.differentiableAt_Gammaℝ_of_nonpole hq
  have hn := AnalyticNumberTheory.DirichletLFunction.Gammaℝ_ne_zero_of_half_ne_neg_nat hp
  have hm := AnalyticNumberTheory.DirichletLFunction.Gammaℝ_ne_zero_of_half_ne_neg_nat hq
  have hχ : backlundChi s ≠ 0 := div_ne_zero hm hn
  have hg : DifferentiableAt ℂ (fun z : ℂ => 1 - z) s := differentiableAt_id.const_sub 1
  have hχd : DifferentiableAt ℂ backlundChi s := by
    change DifferentiableAt ℂ ((fun z : ℂ => Complex.Gammaℝ (1 - z)) / Complex.Gammaℝ) s
    exact (he.comp s hg).div hd hn
  have hz' : riemannZeta (1 - s) ≠ 0 := by
    intro hzero
    have h := zeta_backlund_functional_eq hs
    rw [hzero, mul_zero] at h
    exact hz h
  have hζd : DifferentiableAt ℂ (riemannZeta ∘ fun z : ℂ => 1 - z) s :=
    (differentiableAt_riemannZeta ht1).comp s hg
  have hev : riemannZeta =ᶠ[nhds s] (backlundChi * (riemannZeta ∘ fun z : ℂ => 1 - z)) := by
    have hopen : IsOpen {z : ℂ | z.im ≠ 0} := isOpen_ne.preimage Complex.continuous_im
    filter_upwards [hopen.mem_nhds hs] with z hz'
    exact zeta_backlund_functional_eq hz'
  have hld :
    logDeriv riemannZeta s = logDeriv (backlundChi * (riemannZeta ∘ fun z : ℂ => 1 - z)) s := by
    rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
  have hc : logDeriv (riemannZeta ∘ fun z : ℂ => 1 - z) s = -logDeriv riemannZeta (1 - s) := by
    have hc :=
      logDeriv_comp (f := riemannZeta) (g := fun z : ℂ => 1 - z) (differentiableAt_riemannZeta ht1)
        hg
    have hder : deriv (fun z : ℂ => 1 - z) s = -1 := by
      change deriv (fun z : ℂ => 1 - id z) s = -1
      exact ((hasDerivAt_id s).const_sub 1).deriv
    simp only [hder, mul_neg, mul_one] at hc
    exact hc
  rw [logDeriv_mul s hχ hz' hχd hζd, hc] at hld
  rw [hld]
  ring

/-- At positive height and a nonzero right-side zeta value, the difference
of the imaginary zeta logarithmic derivatives at reflected abscissae equals
the imaginary logarithmic derivative of the Backlund factor. Conjugation
turns `1 - s` into the left point at the same positive height. -/
theorem zeta_reflected_logDeriv_im {T u : ℝ} (hT : 0 < T)
    (hz : riemannZeta (((1 / 2 + u : ℝ) : ℂ) + (T : ℂ) * Complex.I) ≠ 0) :
    (logDeriv riemannZeta (((1 / 2 + u : ℝ) : ℂ) + (T : ℂ) * Complex.I)).im -
        (logDeriv riemannZeta (((1 / 2 - u : ℝ) : ℂ) + (T : ℂ) * Complex.I)).im =
      (logDeriv backlundChi (((1 / 2 + u : ℝ) : ℂ) + (T : ℂ) * Complex.I)).im := by
  let s : ℂ := (((1 / 2 + u : ℝ) : ℂ) + (T : ℂ) * Complex.I)
  let w : ℂ := (((1 / 2 - u : ℝ) : ℂ) + (T : ℂ) * Complex.I)
  have hsi : s.im ≠ 0 := by
    dsimp only [s]
    simpa only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
      Complex.I_re, mul_one, mul_zero, zero_add, add_zero] using hT.ne'
  have he : 1 - s = (starRingEnd ℂ) w := by
    dsimp only [s, w]
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg]
    push_cast
    ring
  have h := congrArg Complex.im (zeta_backlund_logDeriv hsi hz)
  rw [Complex.add_im, he, zeta_logDeriv_conj, Complex.conj_im] at h
  exact h

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
