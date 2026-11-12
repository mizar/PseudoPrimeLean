/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalEnvelope
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosal40000Bounds
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosal39760Sharp

/-! # Lee–Nosal error bound on the uniform entrance interval -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- For `39760 ≤ x ≤ 40000`, the unconditional Lee–Nosal psi error inequality follows
from certified endpoint bounds and monotonicity of `psi`. -/
theorem psi_lee_nosal_39760_40000 {x : ℝ} (ha : 39760 ≤ x) (hb : x ≤ 40000) :
    |Chebyshev.psi x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  apply
    (show |Chebyshev.psi x - x| ≤ (600 : ℝ) by
        apply abs_le.mpr
        have hl := Chebyshev.psi_mono ha
        have hu := Chebyshev.psi_mono hb
        have hp := psi_39760_sharp_lower
        have hq := psi_40000_bounds.2
        constructor <;> linarith only [ha, hb, hl, hu, hp, hq]).trans
  exact lee_nosal_envelope_ge_600 ha (hb.trans (by norm_num only))

/-- At `x = 40000`, the Lee–Nosal psi error inequality holds unconditionally.
A kernel-certified lcm checkpoint gives absolute error at most 14, which is below
its Lee–Nosal envelope. This is one point, not an interval certificate. -/
theorem psi_lee_nosal_40000 :
    |Chebyshev.psi 40000 - 40000| ≤
      Real.sqrt 40000 *
        (Real.log 40000 * (Real.log 40000 - Real.log (Real.log 40000)) / (8 * Real.pi)) := by
  exact psi_lee_nosal_39760_40000 (by norm_num only) le_rfl

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
