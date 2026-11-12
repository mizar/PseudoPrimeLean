/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalEnvelope
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosal40000Bounds
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosal40512

/-! # A finite Lee–Nosal error bound -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- For `40000 ≤ x ≤ 40512`, the unconditional Lee–Nosal psi error inequality follows
from the certified endpoint bounds and monotonicity of `psi`. -/
theorem psi_lee_nosal_40000_40512 {x : ℝ} (ha : 40000 ≤ x) (hb : x ≤ 40512) :
    |Chebyshev.psi x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  apply
    (show |Chebyshev.psi x - x| ≤ (600 : ℝ) by
        apply abs_le.mpr
        have hl := Chebyshev.psi_mono ha
        have hu := Chebyshev.psi_mono hb
        have hp := psi_40000_bounds.1
        have hq := psi_40512_upper
        constructor <;> linarith only [ha, hb, hl, hu, hp, hq]).trans
  exact lee_nosal_envelope_ge_600 (by linarith only [ha]) (by linarith only [hb])

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
