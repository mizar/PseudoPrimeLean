/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# Conjugation of the digamma function

Transfer gamma conjugation to its derivative and logarithmic derivative.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Gamma

/-- At every complex argument, digamma commutes with conjugation. Differentiate
Gamma's conjugation identity and conjugate its quotient. This supplies the dual
archimedean logarithmic derivative, including its total values at gamma poles. -/
theorem digamma_conj (s : ℂ) :
    Complex.digamma ((starRingEnd ℂ) s) = (starRingEnd ℂ) (Complex.digamma s) := by
  have he : (star ∘ Complex.Gamma ∘ star) = Complex.Gamma := by
    funext z
    simp only [Function.comp_def, Complex.star_def, Complex.Gamma_conj, Complex.conj_conj]
  have hd := congrFun (deriv_star_conj (f := Complex.Gamma)) (star s)
  simp only [Complex.star_def, Function.comp_def, Complex.conj_conj] at he hd
  rw [he] at hd
  simp only [Complex.digamma, logDeriv_apply, map_div₀]
  rw [hd, Complex.Gamma_conj]

end PseudoPrime.AnalyticNumberTheory.Gamma
