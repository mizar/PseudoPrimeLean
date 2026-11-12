/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalEnvelope
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosal42560Lower
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosal42816Upper

/-! # A finite Lee–Nosal error bound -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The Lee–Nosal psi error bound holds unconditionally on `[42560, 42816]`.
Certified endpoint bounds and monotonicity give an error of at most 600. -/
theorem psi_lee_nosal_42560_42816 {x : ℝ} (ha : 42560 ≤ x) (hb : x ≤ 42816) :
    |Chebyshev.psi x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  apply
    (show |Chebyshev.psi x - x| ≤ (600 : ℝ) by
        apply abs_le.mpr
        have hl := Chebyshev.psi_mono ha
        have hu := Chebyshev.psi_mono hb
        have hp := psi_42560_lower
        have hq := psi_42816_upper
        constructor <;> linarith only [ha, hb, hl, hu, hp, hq]).trans
  exact lee_nosal_envelope_ge_600 (by linarith only [ha]) (by linarith only [hb])

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
