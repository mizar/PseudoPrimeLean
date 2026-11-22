/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

import PseudoPrime.AnalyticNumberTheory.Arithmetic.EulerFiveHalvesBound
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.Basic
public import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-! # A uniform Euler bound on the half-plane beyond five halves -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- For any Dirichlet character, `σ ≥ 5 / 2`, and real height `t`, the ordinary
L-function logarithmic derivative has norm at most `1 / 2`. The Euler-series
majorant and a rationally certified Mangoldt bound give this unconditional estimate.
It supplies the ordinary Euler term in explicit Dirichlet zero-tail bounds. -/
theorem norm_logDeriv_le_half {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {σ : ℝ}
    (hσ : (5 / 2 : ℝ) ≤ σ) (t : ℝ) :
    ‖logDeriv χ.LFunction ((σ : ℂ) + t * Complex.I)‖ ≤ (1 / 2 : ℝ) := by
  have h := norm_logDeriv_L_le_mangoldt_tsum χ (by linarith only [hσ] : 1 < σ) t
  simp only [neg_div, norm_neg] at h
  exact h.trans (Arithmetic.tsum_vonMangoldt_le_half hσ)

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
