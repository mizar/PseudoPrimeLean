/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Calculus.LogDeriv

/-!
# Zero location from the conjugate functional equation

Separate reflection of zeros from right-half-plane nonvanishing.
These elementary implications apply before any critical-line hypothesis.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.General

/-- A function satisfying the conjugate functional equation with nonzero root
number and having no zeros in Re s > 1 has every zero in 0 <= Re s <= 1.
Reflect a hypothetical left-half-plane zero to the zero-free right half-plane.
This is the zero-location step of Lemma 5.5; Euler-product nonvanishing is kept
as an explicit premise, separate from the functional-equation argument. -/
theorem zero_re_mem_Icc_of_functionalEquation {F : ℂ → ℂ} {ε : ℂ} (hε : ε ≠ 0)
    (hfe : ∀ s, F s = ε * star (F (1 - star s))) (hright : ∀ s, 1 < s.re → F s ≠ 0) {ρ : ℂ}
    (hz : F ρ = 0) : 0 ≤ ρ.re ∧ ρ.re ≤ 1 := by
  constructor
  · by_contra h
    have hn : ρ.re < 0 := lt_of_not_ge h
    have hre : 1 < (1 - star ρ).re := by
      simp only [Complex.sub_re, Complex.one_re, Complex.star_def, Complex.conj_re]
      linarith only [hn]
    have hf := hright (1 - star ρ) hre
    have he := hfe ρ
    rw [hz] at he
    exact (mul_ne_zero hε (star_ne_zero.mpr hf)) he.symm
  · by_contra h
    exact hright ρ (lt_of_not_ge h) hz

/-- Under the conjugate functional equation with nonzero root number,
s is a zero exactly when 1-conj(s) is a zero. Nonzero scalar multiplication
and conjugation preserve vanishing. This identifies the reflection used in
the critical-strip zero expansion without assuming the Riemann hypothesis. -/
theorem zero_iff_reflected_zero {F : ℂ → ℂ} {ε : ℂ} (hε : ε ≠ 0)
    (hfe : ∀ s, F s = ε * star (F (1 - star s))) (s : ℂ) : F s = 0 ↔ F (1 - star s) = 0 := by
  rw [hfe s, mul_eq_zero, or_iff_right hε, star_eq_zero]

/-- Differentiability of F at the reflected point gives the derivative of
conj(F(1-conj(z))). Apply conjugate differentiation after the affine change
of variable. The derivative is minus the conjugate derivative of F.
This is the analytic step in differentiating the functional equation. -/
theorem hasDerivAt_conjugateReflection {F : ℂ → ℂ} {s : ℂ}
    (hd : DifferentiableAt ℂ F (1 - star s)) :
    HasDerivAt (fun z ↦ star (F (1 - star z))) (-(star (deriv F (1 - star s)))) s := by
  have h := (hd.hasDerivAt.comp (star s) ((hasDerivAt_id' (star s)).const_sub 1)).star_conj
  simpa only [Function.comp_def, Complex.star_def, map_neg, Complex.conj_conj, mul_neg_one] using h

/-- A conjugate functional equation with nonzero root number reflects
the logarithmic derivative with a minus sign. Differentiate the conjugated
reflection and cancel the constant root number. This eliminates the
Hadamard center constant when comparing reflected points. -/
theorem logDeriv_eq_neg_conjugateReflection {F : ℂ → ℂ} {ε s : ℂ} (hε : ε ≠ 0)
    (hfe : ∀ z, F z = ε * star (F (1 - star z))) (hd : DifferentiableAt ℂ F (1 - star s)) :
    logDeriv F s = -(star (logDeriv F (1 - star s))) := by
  have he : F = fun z ↦ ε * star (F (1 - star z)) := funext hfe
  conv_lhs => rw [he, logDeriv_const_mul s ε hε]
  rw [logDeriv_apply, (hasDerivAt_conjugateReflection hd).deriv, logDeriv_apply]
  simp only [Complex.star_def, map_div₀, neg_div]

end PseudoPrime.AnalyticNumberTheory.General
