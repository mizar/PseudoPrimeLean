/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalEnvelope
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosal42816Lower
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosal43072Upper

/-! # A finite Lee–Nosal error bound -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The Lee–Nosal psi error bound holds unconditionally on `[42816, 43072]`.
Certified endpoint bounds and monotonicity give an error of at most 600. -/
theorem psi_lee_nosal_42816_43072 {x : ℝ} (ha : 42816 ≤ x) (hb : x ≤ 43072) :
    |Chebyshev.psi x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  apply
    (show |Chebyshev.psi x - x| ≤ (600 : ℝ) by
        apply abs_le.mpr
        have hl := Chebyshev.psi_mono ha
        have hu := Chebyshev.psi_mono hb
        have hp := psi_42816_lower
        have hq := psi_43072_upper
        constructor <;> linarith only [ha, hb, hl, hu, hp, hq]).trans
  exact lee_nosal_envelope_ge_600 (by linarith only [ha]) (by linarith only [hb])

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
