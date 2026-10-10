/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannXi.LogDerivZeta
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GammaFactorVerticalGrowth

/-! # Gamma-factor decompositions and reflection of the xi logarithmic derivative

Separate the archimedean and elementary-pole contributions from zeta.
The xi functional equation transfers right-half-plane formulas to the left.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannXi

/-- At a regular zeta point with real part greater than −2, express the ξ logarithmic
derivative using the level-one gamma factor shifted by two. The gamma recurrence
identifies the digamma term. This form supports contour estimates. -/
theorem logDeriv_eq_pole_gammaFactor_zeta_of_regular {s : ℂ} (hs : -2 < s.re) (hn : s ≠ 1)
    (hz : riemannZeta s ≠ 0) :
    logDeriv riemannXi s =
      1 / (s - 1) + logDeriv (1 : DirichletCharacter ℂ 1).gammaFactor (s + 2) +
        logDeriv riemannZeta s := by
  have h1 : (1 : DirichletCharacter ℂ 1).Even := by
    rw [DirichletCharacter.Even, Subsingleton.elim (-1 : ZMod 1) 1, map_one]
  have hp : 0 < (s + 2).re := by
    rw [Complex.add_re, Complex.re_ofNat]
    linarith only [hs]
  have hh : ∀ m : ℕ, (s + 2) / 2 ≠ -(m : ℂ) := by
    simpa only [Complex.ofReal_zero, add_zero] using
      DirichletLFunction.half_add_ne_neg_nat_of_re_pos hp (le_refl (0 : ℝ))
  have hg := DirichletLFunction.logDeriv_gammaFactor_eq_of_even_of_half_ne_neg_nat h1 hh
  rw [show (s + 2) / 2 = s / 2 + 1 by ring] at hg
  rw [logDeriv_eq_pole_gamma_zeta_of_regular hs hn hz, hg]
  ring

/-- To the right of one, ξ separates two elementary poles, the level-one gamma
factor and the zeta logarithmic derivative. The digamma recurrence removes the
shift by two. This form reuses the right-line gamma and Euler integrability bounds. -/
theorem logDeriv_eq_poles_gammaFactor_zeta_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    logDeriv riemannXi s =
      1 / s + 1 / (s - 1) + logDeriv (1 : DirichletCharacter ℂ 1).gammaFactor s +
        logDeriv riemannZeta s := by
  have hp : 0 < s.re := zero_lt_one.trans hs
  have hh : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := by
    simpa only [Complex.ofReal_zero, add_zero] using
      DirichletLFunction.half_add_ne_neg_nat_of_re_pos hp (le_refl (0 : ℝ))
  have hg :=
    DirichletLFunction.logDeriv_gammaFactor_eq_of_even_of_half_ne_neg_nat
      DirichletLFunction.principal_modulus_one_even hh
  rw [logDeriv_eq_pole_gamma_zeta_of_one_lt_re hs, hg, Complex.digamma_apply_add_one (s / 2) hh,
    inv_div]
  ring

/-- The functional equation reverses the sign of the ξ logarithmic derivative.
Differentiate the reflection identity and divide by the equal function values.
The identity also holds at zeros because the logarithmic derivative is totalized. -/
theorem logDeriv_one_sub (s : ℂ) : logDeriv riemannXi (1 - s) = -logDeriv riemannXi s := by
  have h := (differentiable_riemannXi (1 - s)).hasDerivAt.comp s ((hasDerivAt_id s).const_sub 1)
  simp only [Function.comp_def, riemannXi_one_sub] at h
  have hd := h.deriv
  simp only [mul_neg_one] at hd
  change deriv riemannXi (1 - s) / riemannXi (1 - s) = -(deriv riemannXi s / riemannXi s)
  rw [riemannXi_one_sub, hd, neg_div, neg_neg]

end PseudoPrime.AnalyticNumberTheory.RiemannXi
