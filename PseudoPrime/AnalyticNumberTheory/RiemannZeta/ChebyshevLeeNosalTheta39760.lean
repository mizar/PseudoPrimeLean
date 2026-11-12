/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalCells
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalEnvelope
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalPrimePowers
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosal39760Sharp
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosal40000Bounds

/-! # Lee–Nosal theta bound on the lower connecting interval -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The Lee–Nosal theta error bound holds unconditionally on `[39760, 40000]`.
Certified psi endpoints and the prime-power mass bound supply the cell inequalities. -/
theorem theta_lee_nosal_39760_40000 {x : ℝ} (ha : 39760 ≤ x) (hb : x ≤ 40000) :
    |Chebyshev.theta x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  apply theta_lee_nosal_cell (a := 39760) (b := 40000) (c := 600) _ ha hb _ _ _
  · exact Real.exp_one_lt_three.le.trans (by norm_num only)
  · have h := psi_sub_theta_le_300 (x := 39760) (by norm_num only) (by norm_num only)
    linarith only [h, psi_39760_sharp_lower]
  · have ht := Chebyshev.theta_le_psi 40000
    linarith only [ht, psi_40000_bounds.2]
  · exact lee_nosal_envelope_ge_600 (by norm_num only) (by norm_num only)

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
