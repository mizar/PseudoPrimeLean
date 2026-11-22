/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

import PseudoPrime.AnalyticNumberTheory.Gamma.EvenResolventCertificate
import PseudoPrime.AnalyticNumberTheory.Gamma.RealDigammaLogUpper
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # A signed bound for the real Gamma factor -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Gamma

/-- For real `σ ≥ 1`, the real logarithmic derivative of the real Gamma factor is
at most one half of `log (σ / 2) - log π`. The exact gamma-factor decomposition and
the signed real digamma bound supply the estimate. It is used in zero-mass bounds. -/
theorem re_logDeriv_GammaReal_le_log {σ : ℝ} (hσ : 1 ≤ σ) :
    (logDeriv Complex.Gammaℝ (σ : ℂ)).re ≤ (Real.log (σ / 2) - Real.log Real.pi) / 2 := by
  rw [re_logDeriv_Gammaℝ_of_pos (by linarith only [hσ])]
  have h := real_digamma_le_log (x := σ / 2) (by linarith only [hσ])
  linarith only [h]

end PseudoPrime.AnalyticNumberTheory.Gamma
