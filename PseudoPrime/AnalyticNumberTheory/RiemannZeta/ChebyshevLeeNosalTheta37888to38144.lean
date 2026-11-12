/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalCells
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalEnvelope32768
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosal37888Lower
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosal38144Upper
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalPrimePowers

/-! # A finite Lee–Nosal theta error bound -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The Lee–Nosal theta error bound holds unconditionally on `[37888, 38144]`.
Certified endpoint bounds supply the interval criterion. -/
theorem theta_lee_nosal_37888_38144 {x : ℝ} (ha : 37888 ≤ x) (hb : x ≤ 38144) :
    |Chebyshev.theta x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  apply theta_lee_nosal_cell (a := 37888) (b := 38144) (c := 600) _ ha hb _ _ _
  · exact Real.exp_one_lt_three.le.trans (by norm_num only)
  · have h := psi_sub_theta_le_300 (x := 37888) (by norm_num only) (by norm_num only)
    linarith only [h, psi_37888_lower]
  · have ht := Chebyshev.theta_le_psi 38144
    linarith only [ht, psi_38144_upper]
  · exact lee_nosal_envelope_ge_600_of_32768 (by norm_num only)

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
