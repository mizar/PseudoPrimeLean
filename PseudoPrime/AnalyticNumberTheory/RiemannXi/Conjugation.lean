/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannXi.LogDerivGammaFactor
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

/-! # Conjugation symmetry of xi and its logarithmic derivative -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannXi

private theorem completedZetaRegularized_conj (s : ℂ) :
    completedRiemannZeta₀ (starRingEnd ℂ s) = (starRingEnd ℂ) (completedRiemannZeta₀ s) := by
  have h := completedRiemannZeta_conj s
  rw [completedRiemannZeta_eq, completedRiemannZeta_eq] at h
  simp only [map_sub, map_div₀, map_one] at h
  linear_combination h

/-- The entire Riemann xi function commutes with complex conjugation. The
completed zeta conjugation formula and the real polynomial normalization
establish the identity at every complex argument. -/
theorem riemannXi_conj (s : ℂ) : riemannXi (starRingEnd ℂ s) = (starRingEnd ℂ) (riemannXi s) := by
  unfold riemannXi
  simp only [map_add, map_mul, map_sub, map_div₀, map_one, map_ofNat, completedZetaRegularized_conj]

/-- The derivative of xi commutes with complex conjugation. Apply the
conjugated derivative formula to the entire xi symmetry. -/
theorem deriv_riemannXi_conj (s : ℂ) :
    deriv riemannXi (starRingEnd ℂ s) = (starRingEnd ℂ) (deriv riemannXi s) := by
  have heq : (starRingEnd ℂ ∘ riemannXi ∘ starRingEnd ℂ) = riemannXi := by
    funext w
    simp only [Function.comp_apply, riemannXi_conj, starRingEnd_self_apply]
  have h := congrFun (deriv_conj_conj (f := riemannXi)) ((starRingEnd ℂ) s)
  rw [heq] at h
  simpa only [Function.comp_apply, starRingEnd_self_apply] using h

/-- The total logarithmic derivative of xi commutes with conjugation. The
identity holds also at zeros because division is totalized. -/
theorem logDeriv_riemannXi_conj (s : ℂ) :
    logDeriv riemannXi (starRingEnd ℂ s) = (starRingEnd ℂ) (logDeriv riemannXi s) := by
  rw [logDeriv_apply, logDeriv_apply, deriv_riemannXi_conj, riemannXi_conj, map_div₀]

/-- Reflection across the critical line negates the conjugate logarithmic
derivative. Combine xi's functional equation with conjugation symmetry. -/
theorem logDeriv_riemannXi_reflect (s : ℂ) :
    logDeriv riemannXi (1 - starRingEnd ℂ s) = -(starRingEnd ℂ) (logDeriv riemannXi s) := by
  rw [logDeriv_one_sub, logDeriv_riemannXi_conj]

/-- The xi logarithmic derivative is real on the real axis. Conjugation
fixes a real argument and therefore fixes its logarithmic derivative. -/
theorem logDeriv_riemannXi_real_im (x : ℝ) : (logDeriv riemannXi (x : ℂ)).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  simpa only [Complex.conj_ofReal] using (logDeriv_riemannXi_conj (x : ℂ)).symm

/-- At a fixed real height, reflecting the real coordinate across `1/2`
negates the conjugate logarithmic derivative. This is the pointwise edge
symmetry used to pair the two sides of an upper rectangle. -/
theorem logDeriv_riemannXi_reflect_xy (x y : ℝ) :
    logDeriv riemannXi (((1 - x : ℝ) : ℂ) + (y : ℂ) * Complex.I) =
      -(starRingEnd ℂ) (logDeriv riemannXi ((x : ℂ) + (y : ℂ) * Complex.I)) := by
  have he :
    (1 : ℂ) - (starRingEnd ℂ) ((x : ℂ) + (y : ℂ) * Complex.I) =
      (((1 - x : ℝ) : ℂ) + (y : ℂ) * Complex.I) := by
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_sub,
      Complex.ofReal_one]
    ring
  rw [← he, logDeriv_riemannXi_reflect]

/-- For any height, the real-part integral on the left vertical line is
the negative of the corresponding right-line integral. The reflected
logarithmic derivatives are negative conjugates pointwise. -/
theorem logDeriv_upper_vertical_reflect (t : ℝ) :
    (∫ y in (0 : ℝ)..t, (logDeriv riemannXi (((-(1 / 2 : ℝ) : ℝ) : ℂ) + (y : ℂ) * Complex.I)).re) =
      -(∫ y in (0 : ℝ)..t, (logDeriv riemannXi (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)).re) := by
  have he :
    (fun y : ℝ ↦ (logDeriv riemannXi (((-(1 / 2 : ℝ) : ℝ) : ℂ) + (y : ℂ) * Complex.I)).re) =
      (fun y : ℝ ↦ -(logDeriv riemannXi (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)).re) := by
    funext y
    have h := congrArg Complex.re (logDeriv_riemannXi_reflect_xy (3 / 2) y)
    norm_num only at h
    simpa only [Complex.neg_re, Complex.conj_re] using h
  rw [he, intervalIntegral.integral_neg]

/-- At any height, the imaginary-part integrals on the two halves of the
upper horizontal side agree. Reflect the real coordinate across `1/2`
and use the pointwise conjugation symmetry. -/
theorem logDeriv_upper_horizontal_reflect (t : ℝ) :
    (∫ x in (-(1 / 2) : ℝ)..(1 / 2), (logDeriv riemannXi ((x : ℂ) + (t : ℂ) * Complex.I)).im) =
      (∫ x in (1 / 2 : ℝ)..(3 / 2), (logDeriv riemannXi ((x : ℂ) + (t : ℂ) * Complex.I)).im) := by
  let f : ℝ → ℝ := fun x ↦ (logDeriv riemannXi ((x : ℂ) + (t : ℂ) * Complex.I)).im
  have he : ∀ x : ℝ, f (1 - x) = f x := by
    intro x
    have h := congrArg Complex.im (logDeriv_riemannXi_reflect_xy x t)
    simpa only [f, Complex.neg_im, Complex.conj_im, neg_neg] using h
  have hs := intervalIntegral.integral_comp_sub_left f (a := (1 / 2 : ℝ)) (b := (3 / 2 : ℝ)) 1
  simp only [show (1 : ℝ) - 3 / 2 = -(1 / 2) by norm_num only,
    show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num only] at hs
  simpa only [he] using hs.symm

end PseudoPrime.AnalyticNumberTheory.RiemannXi
