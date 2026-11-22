/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

import PseudoPrime.AnalyticNumberTheory.Gamma.RealGammaLogUpper
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.CompletedVerticalGrowth
public import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-! # A signed Gamma-factor bound at a real zero-mass parameter -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- For any character and real `H ≥ 2`, the gamma-factor logarithmic derivative at
`H + 1/2` is at most `(log H - log π) / 2`. The two character parities reduce to the
real Gamma factor at arguments differing by one, and each logarithm is at most `log H`.
This is the archimedean term in the explicit zero-mass bound. -/
theorem re_gammaLogDeriv_le_log {q : ℕ} (χ : DirichletCharacter ℂ q) {H : ℝ} (hH : 2 ≤ H) :
    (logDeriv χ.gammaFactor (((H + 1 / 2 : ℝ) : ℂ))).re ≤ (Real.log H - Real.log Real.pi) / 2 := by
  let σ : ℝ := H + 1 / 2
  have hs : 1 ≤ σ := by
    dsimp only [σ]; linarith only [hH]
  have ht : 1 ≤ σ + 1 := by linarith only [hs]
  have ha := Gamma.re_logDeriv_GammaReal_le_log hs
  have hb := Gamma.re_logDeriv_GammaReal_le_log ht
  have hlog1 : Real.log (σ / 2) ≤ Real.log H :=
    Real.log_le_log (by linarith only [hs])
      (by
        dsimp only [σ]; linarith only [hH])
  have hlog2 : Real.log ((σ + 1) / 2) ≤ Real.log H :=
    Real.log_le_log (by linarith only [ht])
      (by
        dsimp only [σ]; linarith only [hH])
  have heq :=
    gammaLogDeriv_eq_one_or_shift χ (s := (σ : ℂ))
      (by simpa only [Complex.ofReal_re] using (show 0 < σ by linarith only [hs]))
  have hg : (1 : DirichletCharacter ℂ 1).gammaFactor = Complex.Gammaℝ := by
    funext z
    exact principal_modulus_one_even.gammaFactor_def z
  rcases heq with he | he
  · rw [hg] at he
    change (logDeriv χ.gammaFactor (σ : ℂ)).re ≤ _
    rw [he]
    linarith only [ha, hlog1]
  · rw [hg] at he
    change (logDeriv χ.gammaFactor (σ : ℂ)).re ≤ _
    rw [he, ← Complex.ofReal_one, ← Complex.ofReal_add]
    linarith only [hb, hlog2]

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
