/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalEnvelope
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosal40512Lower
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosal41024

/-! # A finite Lee–Nosal error bound -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The unconditional Lee–Nosal psi error bound holds on `[40512, 41024]`.
Certified endpoint inequalities and monotonicity give an error of at most 600. -/
theorem psi_lee_nosal_40512_41024 {x : ℝ} (ha : 40512 ≤ x) (hb : x ≤ 41024) :
    |Chebyshev.psi x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  apply
    (show |Chebyshev.psi x - x| ≤ (600 : ℝ) by
        apply abs_le.mpr
        have hl := Chebyshev.psi_mono ha
        have hu := Chebyshev.psi_mono hb
        have hp := psi_40512_lower
        have hq := psi_41024_upper
        constructor <;> linarith only [ha, hb, hl, hu, hp, hq]).trans
  exact lee_nosal_envelope_ge_600 (by linarith only [ha]) (by linarith only [hb])

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
