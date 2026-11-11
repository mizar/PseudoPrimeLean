/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

/-! # Conjugation of the zeta logarithmic derivative -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The total logarithmic derivative of zeta commutes with conjugation.
Differentiate the conjugation identity and conjugate its quotient; the
identity also holds at points where the totalized logarithmic derivative is
zero. -/
theorem zeta_logDeriv_conj (s : ℂ) :
    logDeriv riemannZeta ((starRingEnd ℂ) s) = (starRingEnd ℂ) (logDeriv riemannZeta s) := by
  have he : (star ∘ riemannZeta ∘ star) = riemannZeta := by
    funext z
    simp only [Function.comp_def, Complex.star_def, riemannZeta_conj, Complex.conj_conj]
  have hd := congrFun (deriv_star_conj (f := riemannZeta)) (star s)
  simp only [Complex.star_def, Function.comp_def, Complex.conj_conj] at he hd
  rw [he] at hd
  simp only [logDeriv_apply, map_div₀]
  rw [hd, riemannZeta_conj]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
