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
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosal47408ThetaLower
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosal47680Upper

/-! # Finite Lee–Nosal theta error bound -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The unconditional Lee–Nosal theta error bound holds on `[47408, 47634]`.
The proof uses independent psi endpoint and prime-power mass certificates. -/
theorem theta_lee_nosal_47408_47634 {x : ℝ} (ha : 47408 ≤ x) (hb : x ≤ 47634) :
    |Chebyshev.theta x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  apply theta_lee_nosal_cell (a := 47408) (b := 47634) (c := 600) _ ha hb _ _ _
  · exact Real.exp_one_lt_three.le.trans (by norm_num only)
  · have h := psi_sub_theta_le_300 (x := 47408) (by norm_num only) (by norm_num only)
    linarith only [h, psi_47408_theta_lower]
  · have hm := Chebyshev.psi_mono (show (47634 : ℝ) ≤ 47680 by norm_num only)
    have ht := Chebyshev.theta_le_psi 47634
    linarith only [hm, ht, psi_47680_upper]
  · exact lee_nosal_envelope_ge_600 (by norm_num only) (by norm_num only)

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
